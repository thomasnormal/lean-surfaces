import Examples.«system-verilog».comb_shift.gen
import LeanModels.Sv.CombProcTactic

/-!
# Shifts of an operation: what stays refused, and why

The left operand of a shift may be any expression of the fragment, its conversion markers included (`comb_proof.lean`:
`shift_parts`, `shift_signed`). What stays outside names its wall:

* `neg/sh_nested_signed.sv`: `((a >>> 1) + b) << 1` with a signed `a` and an unsigned `b`: the sum is unsigned, so slang
  converts `a` and the inner shift is `>>>` of an unsigned operand (`u>>>`, a logical shift), which `instDivOperand2`
  lowers to `BinOp.ashr false`, an operator the skeleton does not build yet;
* `neg/sh_cat_op.sv`: `{a >>> 1, b} << 1`: an OPERATION as a concatenation part (a part is read as a sized literal, one
  access or a replication, as everywhere);
* `neg/sh_self_asr.sv`: `(|(a >>> 2)) << 1`: an arithmetic shift in a self-determined position (the operand of a
  reduction) inside the shift operand; self-determined operands are read as the v1 fragment, which has no shift;
* `neg/sh_ashl.sv`: `(a + b) <<< 1`: `<<<` of an unsigned operand (the same as `<<`, IEEE 1800-2023 §11.4.10), which
  `instExpr2` lowers to `BinOp.ashl`, an operator the skeleton does not build yet.

The amount of a shift is still a leaf (a signal access, a sized literal, an unsized constant, a bare genvar or parameter):
`comb_word/comb_errors.lean` pins `a << (s + 3'd1)`, `a << (N - 1)` and `a << (i + 1)`.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_shift.comb_errors

load_design_sv2 sh_nested_signed from "Examples/system-verilog/comb_shift/neg/sh_nested_signed.sv.json"
load_design_sv2 sh_cat_op from "Examples/system-verilog/comb_shift/neg/sh_cat_op.sv.json"
load_design_sv2 sh_self_asr from "Examples/system-verilog/comb_shift/neg/sh_self_asr.sv.json"
load_design_sv2 sh_ashl from "Examples/system-verilog/comb_shift/neg/sh_ashl.sv.json"

/--
error: sv_structure: outside the supported fragment — site `plain#0`: `>>>` inside the left operand of a shift whose operand is unsigned (`u>>>`, IEEE 1800-2023 §11.4.10: a logical shift there): `instDivOperand2` lowers it to `BinOp.ashr false`, an operator the tactics do not read yet (they read `<<`, `>>` and the arithmetic `>>>` of a signed operand)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sh_nested_signed.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a concatenation part that is an operation (`s>>>`) inside the left operand of a shift (outside the fragment: a part is read as a sized literal, one access or a replication)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sh_cat_op.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: an arithmetic shift right `>>>` in a self-determined position (an operand of `&&`, `||`, `!`, a reduction, a comparison or the condition of `?:`): the fragment reads `>>>` of a signed operand as a right-hand side or an operand of the word-level operators, not here
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sh_self_asr.sem W) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: operator `u<<<` is outside the v1 fragment (it has the bitwise gates `&`, `|`, `^`, the word-level `+`, `-` and `*`, the six comparisons, the four signed comparisons of two signed signals, the run-time shifts `<<` and `>>`, the arithmetic shift `>>>` of a signed operand and the logical `&&`, `||`; `<<<` and `>>>` of an unsigned operand (the same as `<<` and `>>`, but lowered to `BinOp.ashl`/`BinOp.ashr false`), a signed `>>`, `/`, `%` and `**` are word-level operators it does not have yet)
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) : CombDesign (sh_ashl.sem W) := by
  sv_structure

end Examples.«system-verilog».comb_shift.comb_errors
