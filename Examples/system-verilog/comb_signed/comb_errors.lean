import Examples.«system-verilog».comb_signed.gen
import LeanModels.Sv.CombProcTactic

/-!
# Signed reads: what stays refused, and why

The tactics read a signed signal as the same bits wherever it is a whole operand of a continuous assign, and a signed
comparison of two signed signals declared with the same dimensions as the two's-complement order (`comb_proof.lean`).
The constructs whose meaning signedness changes and that they do not read yet are refused, each with its reason. (A part
select of a signed signal as the left operand of a shift, and an arithmetic shift right into a target wider than its
operand, were refused here; the left operand of a shift is now read through `instDivOperand2` at the signedness of the
shift, and both are proved in `comb_shift/comb_proof.lean`, `shift_signed_correct`.)

* `neg/sg_sel_proc.sv`: a bit select of a signed signal inside `always_comb`;
* `neg/sg_cmp_dims.sv`: a signed comparison of `logic signed [W-1:0] a` and `logic signed [7:0] b` (equal widths at
  `W = 8` only; elsewhere the narrower operand is sign-extended, IEEE 1800-2023 §11.8.2);
* `neg/sg_cmp_self.sv`: a signed comparison as an operand of `&&` (a self-determined position);
* `neg/sg_cmp_opd.sv`: a signed comparison whose operand is an expression `a + b`, not a whole signed signal;
* `neg/sg_cmp_proc.sv`: a signed comparison inside `always_comb`;
* `neg/sg_asr_amt.sv`: an arithmetic shift right by a signed amount `a >>> b`;
* `neg/sg_asr_self.sv`: an arithmetic shift right as an operand of `&&`;
* `neg/asr_unsigned.sv`: `>>>` of an unsigned operand;
* `neg/sg_cmp_const.sv` (the downstream clean-room repro `signed_decl.sv`, verbatim): `x >= 0` with `x` signed and 8 bits
  wide. The unsized `0` is a 32-bit signed integer, so the comparison is signed and `x` is sign-extended to 32 bits
  (IEEE 1800-2023 §11.8.1, §11.4.4). The extractor marks that sign extension `ConversionExpression:width`: the envelope
  carries an `Unsupported` node in place of `x`, `instExpr2` keeps it, and the semantics itself lowers the site to a loud
  node, so no equation holds for any tactic to prove. The wall is the extractor's (the `SignedResize` marker it emits for
  the operand of a shift or a division), and the message says so;
* `neg/sg_cmp_mixed.sv`: a signed comparison of an 8-bit and a 16-bit signed signal, the same wall (the narrower operand
  is sign-extended, §11.8.2).
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_signed.comb_errors

load_design_sv2 sg_sel_proc from "Examples/system-verilog/comb_signed/neg/sg_sel_proc.sv.json"
load_design_sv2 sg_cmp_dims from "Examples/system-verilog/comb_signed/neg/sg_cmp_dims.sv.json"
load_design_sv2 sg_cmp_self from "Examples/system-verilog/comb_signed/neg/sg_cmp_self.sv.json"
load_design_sv2 sg_cmp_opd from "Examples/system-verilog/comb_signed/neg/sg_cmp_opd.sv.json"
load_design_sv2 sg_cmp_proc from "Examples/system-verilog/comb_signed/neg/sg_cmp_proc.sv.json"
load_design_sv2 sg_asr_amt from "Examples/system-verilog/comb_signed/neg/sg_asr_amt.sv.json"
load_design_sv2 sg_asr_self from "Examples/system-verilog/comb_signed/neg/sg_asr_self.sv.json"
load_design_sv2 asr_unsigned from "Examples/system-verilog/comb_signed/neg/asr_unsigned.sv.json"
load_design_sv2 sg_cmp_const from "Examples/system-verilog/comb_signed/neg/sg_cmp_const.sv.json"
load_design_sv2 sg_cmp_mixed from "Examples/system-verilog/comb_signed/neg/sg_cmp_mixed.sv.json"

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
error: sv_structure: outside the supported fragment — site `plain#0`: operator `u>>>` is outside the v1 fragment (it has the bitwise gates `&`, `|`, `^`, the word-level `+`, `-` and `*`, the six comparisons, the four signed comparisons of two signed signals, the run-time shifts `<<` and `>>`, the arithmetic shift `>>>` of a signed operand and the logical `&&`, `||`; `<<<` and `>>>` of an unsigned operand (the same as `<<` and `>>`, but lowered to `BinOp.ashl`/`BinOp.ashr false`), a signed `>>`, `/`, `%` and `**` are word-level operators it does not have yet)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (asr_unsigned.sem W) := by
  sv_structure

-- the downstream repro: the envelope itself refuses the sign extension of `x` (`ConversionExpression:width`)
/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison whose operand the envelope marks `ConversionExpression:width`: the extractor refuses the sign extension of a signed operand narrower than the comparison (`x >= 0` with a signed `x` of fewer than 32 bits: the unsized `0` is a 32-bit signed integer, so `x` is sign-extended, IEEE 1800-2023 §11.8.1, §11.4.4; likewise two signed signals of different widths), so the semantics lowers this site to a loud node and no equation holds for it. The fix belongs to the extractor (the `SignedResize` marker it emits for the operand of a shift or a division), not to the tactics
-/
#guard_msgs (whitespace := lax) in
example : CombDesign sg_cmp_const.sem := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison whose operand the envelope marks `ConversionExpression:width`: the extractor refuses the sign extension of a signed operand narrower than the comparison (`x >= 0` with a signed `x` of fewer than 32 bits: the unsized `0` is a 32-bit signed integer, so `x` is sign-extended, IEEE 1800-2023 §11.8.1, §11.4.4; likewise two signed signals of different widths), so the semantics lowers this site to a loud node and no equation holds for it. The fix belongs to the extractor (the `SignedResize` marker it emits for the operand of a shift or a division), not to the tactics
-/
#guard_msgs (whitespace := lax) in
example : CombDesign sg_cmp_mixed.sem := by
  sv_structure

end Examples.«system-verilog».comb_signed.comb_errors
