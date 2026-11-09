import Examples.«system-verilog».comb_shift.gen
import LeanModels.Sv.CombProcTactic

/-!
# Shifts of an operation: what stays refused, and why

The left operand of an UNSIGNED shift may be any expression of the word-level fragment (`comb_proof.lean`). What stays
outside names its wall:

* `neg/sh_signed_op.sv`: `(a + b) >>> 1` of signed `a`, `b`: the left operand of a SIGNED shift (`>>>`, or `<<` of a
  signed operand) is read as a signal access, a sized literal or an unsized constant. (Its operation would be lowered by
  `instDivOperand2` with every leaf SIGN-extended to the context; the mirror `Sk.dz` has that case, `Sk.fit true`, but the
  recognizer reads a signed read inside an operation only through the unsigned twin, which does not enter a shift.)
* `neg/sh_nested_signed.sv`: `((a >>> 1) + b) << 1` with a signed `a` and an unsigned `b`: the sum is unsigned, so slang
  converts `a` and the inner shift is `>>>` of an unsigned operand (`u>>>`), an operator the fragment does not read yet.

The amount of a shift is still a leaf (a signal access, a sized literal, an unsized constant, a bare genvar or parameter):
`comb_word/comb_errors.lean` pins `a << (s + 3'd1)`, `a << (N - 1)` and `a << (i + 1)`.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_shift.comb_errors

load_design_sv2 sh_signed_op from "Examples/system-verilog/comb_shift/neg/sh_signed_op.sv.json"
load_design_sv2 sh_nested_signed from "Examples/system-verilog/comb_shift/neg/sh_nested_signed.sv.json"

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a shift amount, or the left operand of a signed shift, that is not a signal access, a sized literal or an unsized constant (outside the fragment: these two positions are read as one of these, the amount also as a bare genvar or parameter; an expression there, such as `s + 1` as an amount or `(a + b) >>> 1`, is not read yet: write it into a signal first. The left operand of an unsigned shift may be any expression the fragment reads)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sh_signed_op.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: operator `u>>>` is outside the v1 fragment (it has the bitwise gates `&`, `|`, `^`, the word-level `+`, `-` and `*`, the six comparisons, the four signed comparisons of two signed signals, the run-time shifts `<<` and `>>`, the arithmetic shift `>>>` of a signed operand and the logical `&&`, `||`; `<<<`, `>>>` of an unsigned operand, a signed `>>`, `/`, `%` and `**` are word-level operators it does not have yet)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sh_nested_signed.sem W) := by
  sv_structure

end Examples.«system-verilog».comb_shift.comb_errors
