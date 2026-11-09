import Examples.«system-verilog».comb_word.gen
import LeanModels.Sv.CombProcTactic

/-!
# What stays outside the word-level fragment, and the message (WP-B2)

Each negative design has ONE defect and is refused with a tactic message that names the site (the first line is
what the checker's `--tactics` advisory reports as `in_fragment false`):

* `neg_trunc`, `neg_unsized`: a width conversion around an OPERATION (a sum into a narrower target; `a + 1`, whose
  unsized constant makes the sum 32 bits wide and truncated): refused in gate 1, accepted since gate 2b (guards below;
  the real designs are `trunc_inc`);
* `neg_mul_op`: a product neither of whose factors is a signal access (`(a + b) * (a - b)`): the elaboration folds a
  product of constants, so the fragment reads `*` with one signal-access factor (`neg_mul`, `a * b`, is accepted since
  `*` joined the fragment: `mul_word`; `neg_lt`, an ordering comparison, since gate 2b: `cmp_same`; `neg_shift`, `a << 1`,
  since gate 3: `shl_const`);
* `neg_shift_amt`, `neg_shift_par` (gate 3): a shift whose AMOUNT is an expression (`a << (s + 3'd1)`) or an expression
  over a parameter (`a << (N - 1)`): the fragment reads a signal access, a sized literal or an unsized constant there (and a
  bare genvar or parameter), and the message names the amount as the one position still read as a leaf. `neg_shift_op`, a
  shift whose LEFT operand is an operation (`(a + b) << 1`), is accepted since the left operand of a shift is read through
  `instDivOperand2` (`comb_shift`), and proved below by `sv_structure` and `sv_equations`;
* `neg_selfdet`: `+` under a reduction (a self-determined position keeps the v1 fragment);
* `neg_shift_gv` (gate 4b): a shift by an expression over a genvar (`a << (i + 1)`); the bare genvar `a << i` is read;
* `neg_repl_whole`, `neg_repl_nonaffine`, `neg_repl_op`, `neg_repl_selfdet` (gate 4c): a replication of a WHOLE signal (`{2{a}}`: its width is the
  declared one, replicate a bit or a part select), with a count that is a product of two parameters (`{N*M{a[0]}}`), of an operation
  (`{2{a & b}}`), in a self-determined position (`|{4{a[0]}}`: those operands keep the v1 fragment), and in a leaf of an `always_comb` tree
  (`neg_repl_leaf`: the procedural chain does not carry the scope of a constant of the instance);
* `neg_part_nz`, `neg_row_nz`, `neg_row_3d` (gate 4a): a part select of a declaration whose range is not zero-based
  (`[8:1]`), a whole-row select of a two-dimensional declaration whose first range is not zero-based (`[4:1][2:0]`), and a
  declaration of three packed dimensions: the legacy selects of gate 4a are read over zero-based descending ranges only.

(A sum in an `always_comb` leaf was the seventh negative of gate 1; the procedural chain reads the word-level
fragment since gate 2: `addp`.)
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_word.comb_errors

load_design_sv2 neg_trunc from "Examples/system-verilog/comb_word/neg/neg_trunc.sv.json"
load_design_sv2 neg_mul from "Examples/system-verilog/comb_word/neg/neg_mul.sv.json"
load_design_sv2 neg_mul_op from "Examples/system-verilog/comb_word/neg/neg_mul_op.sv.json"
load_design_sv2 neg_lt from "Examples/system-verilog/comb_word/neg/neg_lt.sv.json"
load_design_sv2 neg_shift from "Examples/system-verilog/comb_word/neg/neg_shift.sv.json"
load_design_sv2 neg_shift_op from "Examples/system-verilog/comb_word/neg/neg_shift_op.sv.json"
load_design_sv2 neg_shift_amt from "Examples/system-verilog/comb_word/neg/neg_shift_amt.sv.json"
load_design_sv2 neg_shift_par from "Examples/system-verilog/comb_word/neg/neg_shift_par.sv.json"
load_design_sv2 neg_unsized from "Examples/system-verilog/comb_word/neg/neg_unsized.sv.json"
load_design_sv2 neg_selfdet from "Examples/system-verilog/comb_word/neg/neg_selfdet.sv.json"
load_design_sv2 neg_shift_gv from "Examples/system-verilog/comb_word/neg/neg_shift_gv.sv.json"
load_design_sv2 neg_part_nz from "Examples/system-verilog/comb_word/neg/neg_part_nz.sv.json"
load_design_sv2 neg_row_nz from "Examples/system-verilog/comb_word/neg/neg_row_nz.sv.json"
load_design_sv2 neg_row_3d from "Examples/system-verilog/comb_word/neg/neg_row_3d.sv.json"
load_design_sv2 neg_repl_whole from "Examples/system-verilog/comb_word/neg/neg_repl_whole.sv.json"
load_design_sv2 neg_repl_nonaffine from "Examples/system-verilog/comb_word/neg/neg_repl_nonaffine.sv.json"
load_design_sv2 neg_repl_op from "Examples/system-verilog/comb_word/neg/neg_repl_op.sv.json"
load_design_sv2 neg_repl_selfdet from "Examples/system-verilog/comb_word/neg/neg_repl_selfdet.sv.json"
load_design_sv2 neg_repl_leaf from "Examples/system-verilog/comb_word/neg/neg_repl_leaf.sv.json"

-- a sum into a NARROWER target: accepted since WP-B2 gate 2b (see `trunc_inc`)
#guard neg_trunc.pdesign.summary.toOption.isSome

-- `a * b`: accepted since `*` joined the fragment (see `mul_word`)
#guard neg_mul.pdesign.summary.toOption.isSome

-- a product of two operations: neither factor is a signal access
/--
error: sv_structure: outside the supported fragment — site `plain#0`: a product neither of whose factors is a signal access (outside the v1 fragment: the elaboration folds a product of constants, so `*` is read with at least one factor a signal access, bare or zero-extended; write one factor into a signal first)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_mul_op.sem N) := by
  sv_structure

-- an ordering comparison: accepted since WP-B2 gate 2b (see `cmp_same`)
#guard neg_lt.pdesign.summary.toOption.isSome

-- a shift by an unsized constant (`a << 1`): accepted since WP-B2 gate 3 (see `shl_const`)
#guard neg_shift.pdesign.summary.toOption.isSome

-- a shift whose left operand is an operation (`(a + b) << 1`): accepted since the left operand of a shift is read through
-- `instDivOperand2` (`skD`; the equation of the same shape is proved in `comb_shift`, `shift_op_correct`): the structure
-- stage passes, for every width
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) :
    CombDesign (neg_shift_op.sem N) ∧ Acyclic (neg_shift_op.sem N) := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

-- a shift whose amount is an expression
/--
error: sv_structure: outside the supported fragment — site `plain#0`: a shift amount that is not a signal access, a sized literal, an unsized constant, or a bare genvar or parameter (outside the fragment: the amount of a shift is read as one of these; an expression there, such as `s + 1`, is not read yet. The left operand of a shift may be any expression the fragment reads)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_shift_amt.sem N) := by
  sv_structure

-- a shift by an expression over a parameter
/--
error: sv_structure: outside the supported fragment — site `plain#0`: a shift amount that is not a signal access, a sized literal, an unsized constant, or a bare genvar or parameter (outside the fragment: the amount of a shift is read as one of these; an expression there, such as `s + 1`, is not read yet. The left operand of a shift may be any expression the fragment reads)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_shift_par.sem N) := by
  sv_structure

-- an unsized constant operand (`a + 1`): accepted since WP-B2 gate 2b (see `trunc_inc`)
#guard neg_unsized.pdesign.summary.toOption.isSome

-- a sum in a SELF-determined position (the operand of a reduction): those operands keep the v1 fragment
/--
error: sv_structure: outside the supported fragment — site `plain#0`: operator `+` is outside the v1 fragment here (it has the bitwise gates `&`, `|`, `^`, the logical `&&`, `||` and `==`, `!=`; the word-level `+`, `-` and `*` are accepted only at the context-determined positions of a right-hand side (an `assign` or an `always_comb` leaf), not under `!`, a reduction, a comparison or a `?:` condition; so are the six comparisons and the run-time shifts `<<`, `>>`; `<<<`, `>>>`, a signed `>>`, `/`, `%` and `**` are word-level operators it does not have yet)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_selfdet.sem N) := by
  sv_structure

-- a part select of a vector whose range is not zero-based
/--
error: sv_structure: outside the supported fragment — site `plain#0`: `v`: part selects need a zero-based descending dimension `[hi:0]`
-/
#guard_msgs (whitespace := lax) in
example : CombDesign (neg_part_nz.sem) := by
  sv_structure

-- a whole row of a two-dimensional declaration whose first range is not zero-based
/--
error: sv_structure: structural check failed:
  site `plain#0`: the access `r[0]` does not match the declaration of `r` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
  site `plain#1`: the access `r[0]` does not match the declaration of `r` (a select needs zero-based descending packed dimensions `[hi:0]`, with the number of selects the declaration allows)
-/
#guard_msgs (whitespace := lax) in
example : CombDesign (neg_row_nz.sem) := by
  sv_structure

-- three packed dimensions
/--
error: sv_structure: outside the supported fragment — declaration `r`: only scalar, 1-D and 2-D packed declarations are in the v1 fragment
-/
#guard_msgs (whitespace := lax) in
example : CombDesign (neg_row_3d.sem) := by
  sv_structure

-- a shift by an expression over a genvar: only the bare genvar is a constant the recognizer reads
/--
error: sv_structure: outside the supported fragment — site `g#0`: a shift amount that is not a signal access, a sized literal, an unsized constant, or a bare genvar or parameter (outside the fragment: the amount of a shift is read as one of these; an expression there, such as `s + 1`, is not read yet. The left operand of a shift may be any expression the fragment reads)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_shift_gv.sem N) := by
  sv_structure

-- a replication of a whole signal
/--
error: sv_structure: outside the supported fragment — site `plain#0`: replication of a whole signal (outside the v1 fragment: replicate a bit or a part select)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_repl_whole.sem N) := by
  sv_structure

-- a replication count that is a product of two parameters
/--
error: sv_structure: outside the supported fragment — site `plain#0`: replication count is not affine (outside the v1 fragment: dynamic or nonlinear)
-/
#guard_msgs (whitespace := lax) in
example (N M : Nat) (hN : 1 ≤ N) : CombDesign (neg_repl_nonaffine.sem N M) := by
  sv_structure

-- the replicated operand is an operation
/--
error: sv_structure: outside the supported fragment — site `plain#0`: expression construct outside the v1 fragment (constant, cast, width conversion or system call)
-/
#guard_msgs (whitespace := lax) in
example : CombDesign (neg_repl_op.sem) := by
  sv_structure

-- a replication in a self-determined position (the operand of a reduction)
/--
error: sv_structure: outside the supported fragment — site `plain#0`: replication (outside the v1 fragment)
-/
#guard_msgs (whitespace := lax) in
example : CombDesign (neg_repl_selfdet.sem) := by
  sv_structure

-- a replication in a leaf of an `always_comb` tree
/--
error: sv_structure: outside the supported fragment — site `plain#0`: right-hand side outside the v1 fragment (a gate tree, a concatenation or a fill)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_repl_leaf.sem.lowerComb = some d' ∧ CombDesign d' := by
  sv_structure

end Examples.«system-verilog».comb_word.comb_errors
