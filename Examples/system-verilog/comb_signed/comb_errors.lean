import Examples.«system-verilog».comb_signed.gen
import LeanModels.Sv.CombProcTactic

/-!
# Signed reads: what stays refused, and why

The tactics read a signed signal as the same bits wherever it is a whole operand of a continuous assign, and a signed
comparison of two signed signals declared with the same dimensions, or of a signed signal with a constant of its width,
as the two's-complement order, and a signed comparison whose narrower operand, a whole signed signal or a sized literal,
is sign-extended to the comparison's width (`SignedResize`, IEEE 1800-2023 §11.8.2; `comb_proof.lean`).
The constructs whose meaning signedness changes and that they do not read yet are refused, each with its reason. (A part
select of a signed signal as the left operand of a shift, and an arithmetic shift right into a target wider than its
operand, were refused here; the left operand of a shift is now read through `instDivOperand2` at the signedness of the
shift, and both are proved in `comb_shift/comb_proof.lean`, `shift_signed_correct`.)

* `neg/sg_sel_proc.sv`: a bit select of a signed signal inside `always_comb`;
* `neg/sg_cmp_dims.sv`: a signed comparison of `logic signed [W-1:0] a` and `logic signed [7:0] b` (equal widths at
  `W = 8` only; elsewhere the narrower operand is sign-extended, IEEE 1800-2023 §11.8.2);
* `neg/sg_cmp_self.sv`: a signed comparison as an operand of `&&` (a self-determined position);
* `neg/sg_cmp_opd.sv`: a signed comparison whose operand is an expression `a + b`, not a whole signed signal or a
  constant;
* `neg/sg_cmp_lit_param.sv`: a signed comparison of `logic signed [W-1:0] x` with the sized literal `8'sd0` (equal
  widths at `W = 8` only; elsewhere one operand is extended, §11.8.2, and the semantics extends a sized literal with
  zeros, not with its sign bit: a defect of the semantics reported to ls-sv, so the fragment reads a literal only against
  a signal of the same constant width);
* `neg/sg_cmp_neg.sv`: a signed comparison with a negated constant `z < -5` (unary minus, the next wall: a negative
  constant is read written as its bits, `scmp_const.sv`);
* `neg/sg_cmp_proc.sv`: a signed comparison inside `always_comb`;
* `neg/sg_asr_amt.sv`: an arithmetic shift right by a signed amount `a >>> b`;
* `neg/sg_asr_self.sv`: an arithmetic shift right as an operand of `&&`;
* `neg/asr_unsigned.sv`: `>>>` of an unsigned operand;
* `neg/sg_cmp_sext_param.sv`: a signal of a parameter width `W` against the sized literal `8'sd0`: at the default
  `W = 8` the literal is as wide as the signal, which carries no marker; at `W < 8` the signal is the narrower operand and
  is sign-extended (IEEE 1800-2023 §11.8.2), so the recognizer reads an unmarked signal against a marked operand only when
  the signal is declared with constant dimensions at least as wide;
* `neg/sg_cmp_sext_op.sv`: `(a + b) >= 0`, the sign-extended operands inside an operation (the sum is taken at the 32
  bits of the constant, IEEE 1800-2023 §11.6.1): an operation as an operand of a signed comparison is outside the
  fragment;
* `neg/sg_cmp_sext_sel.sv`: `$signed(x[3:0]) >= 0`: the extractor keeps the extension of an explicit `$signed(...)` call
  loud (`ConversionExpression:width`), so the semantics lowers the site to a loud node.

The clean-room repro `signed_decl.sv` (`x >= 0` with an 8-bit signed `x`) and the comparison of an 8-bit and a 16-bit
signed signal (`scmp_mixed.sv`) were pinned here, refused as "a signed comparison whose operand the envelope marks
`ConversionExpression:width`": the extractor now marks the sign extension of a plain signed signal `SignedResize`, and the
tactics read it (`Sk.sx`); both are proved in `comb_proof.lean`.
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
load_design_sv2 sg_cmp_sext_param from "Examples/system-verilog/comb_signed/neg/sg_cmp_sext_param.sv.json"
load_design_sv2 sg_cmp_sext_op from "Examples/system-verilog/comb_signed/neg/sg_cmp_sext_op.sv.json"
load_design_sv2 sg_cmp_sext_sel from "Examples/system-verilog/comb_signed/neg/sg_cmp_sext_sel.sv.json"
load_design_sv2 sg_cmp_lit_param from "Examples/system-verilog/comb_signed/neg/sg_cmp_lit_param.sv.json"
load_design_sv2 sg_cmp_neg from "Examples/system-verilog/comb_signed/neg/sg_cmp_neg.sv.json"

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a select of the signed signal `a` in a position the tactics do not read through the unsigned twin (they read a select of a signed signal, an unsigned value, IEEE 1800-2023 §11.8.1, where it is an operand of a continuous assign, the actual of a module's input port or an operand of a shift; an index and an `always_comb` body are outside the fragment)
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
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison with an operation (`+`) as an operand, such as `(a + b) >= 0`: the operation is context-determined, so it is taken at the comparison's width, its signed operands extended with their sign bits where they are narrower (IEEE 1800-2023 §11.6.1, §11.8.2, the envelope's `SignedResize` inside the operation); the fragment reads a signed comparison of whole signed signals, sized literals, unsized constants and sign-extension markers around a whole signed signal or a sized literal, not of an operation
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

-- a signal of a parameter width against a marked literal: refused (at `W < 8` the signal would be extended)
/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison of the signed signal `x`, whose declared width is not a constant (it depends on a parameter), with a sign-extended sized literal of 8 bits: at a point where `x` is narrower than 8 bits it is the operand to extend with its sign bit (IEEE 1800-2023 §11.8.2), which the envelope, elaborated at the default point, does not mark, and the semantics refuses there (`Resize:signed`); the fragment reads such a comparison when `x` is declared with constant dimensions of at least 8 bits
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_cmp_sext_param.sem W) := by
  sv_structure

-- the marked operands inside an operation
/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison with an operation (`+`) as an operand, such as `(a + b) >= 0`: the operation is context-determined, so it is taken at the comparison's width, its signed operands extended with their sign bits where they are narrower (IEEE 1800-2023 §11.6.1, §11.8.2, the envelope's `SignedResize` inside the operation); the fragment reads a signed comparison of whole signed signals, sized literals, unsized constants and sign-extension markers around a whole signed signal or a sized literal, not of an operation
-/
#guard_msgs (whitespace := lax) in
example : CombDesign sg_cmp_sext_op.sem := by
  sv_structure

-- an explicit `$signed(...)` call: the extractor keeps its extension loud
/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison whose operand `$signed(x[3:0])` the envelope marks `ConversionExpression:width`: the extractor refuses the sign extension of this operand (it marks the extension of a plain signed signal or a signed literal `SignedResize`, IEEE 1800-2023 §11.8.2, which the fragment reads, and keeps another conversion, such as an explicit `$signed(...)` call of a select, loud), so the semantics lowers this site to a loud node and no equation holds for it
-/
#guard_msgs (whitespace := lax) in
example : CombDesign sg_cmp_sext_sel.sem := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison of the signed signal `x` with a sized literal of 8 bits, where `x` is not declared with constant dimensions of that width (the fragment reads a signed signal compared with a sized literal when the signal's declared width is a constant equal to the literal's: at another width one operand is extended, IEEE 1800-2023 §11.8.2, and the semantics extends a sized literal with zeros, which the fragment does not read)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sg_cmp_lit_param.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a signed comparison with a negated constant (`x < -5`, `x >= -8'sd3`): unary minus is outside the fragment (it reads a signed comparison of a whole signed signal with a sized literal of its width, a negative one written as its bits such as `8'sb1111_1101`, or with an unsized constant that is not negated)
-/
#guard_msgs (whitespace := lax) in
example : CombDesign sg_cmp_neg.sem := by
  sv_structure

end Examples.«system-verilog».comb_signed.comb_errors
