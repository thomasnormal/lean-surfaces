import Examples.«system-verilog».comb_ops.gen
import LeanModels.Sv.CombProcTactic

/-!
# What stays outside the second fragment, and the message (WP-G S2)

Each negative design has ONE defect; each is refused with a tactic message that names the site (the first
line is what the checker's `--tactics` advisory reports as `in_fragment false`):

* `neg_add`, `neg_cmp`: `+`, `>` are word-level operators;
* `neg_minus`: unary minus is arithmetic;
* `neg_resize`, `neg_lnot_wide`: the operand (`~a` into a wider target) or the one-bit result (`!s` into four
  bits) is not as wide as its context, so slang inserted an implicit zero-extension: a width conversion;
* `neg_fill`: an unbased unsized fill (`'0`) inside a conditional arm (a follow-up: write a sized literal).

Two defects are accepted by the recognizer and fail at the equations stage: `neg_tern_wide` (a multi-bit
condition: the obligation `width` is FALSE, the player writes `|v ? a : b`) and `neg_xarm` (an arm with an
unknown bit: the right-hand side is outside the equation fragment).
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_ops.comb_errors

load_design_sv2 neg_add from "Examples/system-verilog/comb_ops/neg/neg_add.sv.json"
load_design_sv2 neg_minus from "Examples/system-verilog/comb_ops/neg/neg_minus.sv.json"
load_design_sv2 neg_cmp from "Examples/system-verilog/comb_ops/neg/neg_cmp.sv.json"
load_design_sv2 neg_resize from "Examples/system-verilog/comb_ops/neg/neg_resize.sv.json"
load_design_sv2 neg_lnot_wide from "Examples/system-verilog/comb_ops/neg/neg_lnot_wide.sv.json"
load_design_sv2 neg_fill from "Examples/system-verilog/comb_ops/neg/neg_fill.sv.json"
load_design_sv2 neg_tern_wide from "Examples/system-verilog/comb_ops/neg/neg_tern_wide.sv.json"
load_design_sv2 neg_xarm from "Examples/system-verilog/comb_ops/neg/neg_xarm.sv.json"

/--
error: sv_structure: outside the supported fragment — site `plain#0`: operator `+` is outside the v1 fragment (it has the bitwise gates `&`, `|`, `^`, the logical `&&`, `||` and `==`, `!=`; arithmetic, ordering comparisons and shifts are word-level operators)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_add.sem N) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: unary operator `-` or `+` (outside the v1 fragment: it has `~` and `!`)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_minus.sem N) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: operator `>` is outside the v1 fragment (it has the bitwise gates `&`, `|`, `^`, the logical `&&`, `||` and `==`, `!=`; arithmetic, ordering comparisons and shifts are word-level operators)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_cmp.sem N) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: width conversion (an operand is not as wide as its context at the default parameters, so slang inserted an implicit zero-extension or truncation; the v1 fragment needs every operand exactly as wide as its target: widen or narrow it explicitly)
-/
#guard_msgs (whitespace := lax) in
example : CombDesign neg_resize.sem := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: width conversion (an operand is not as wide as its context at the default parameters, so slang inserted an implicit zero-extension or truncation; the v1 fragment needs every operand exactly as wide as its target: widen or narrow it explicitly)
-/
#guard_msgs (whitespace := lax) in
example : CombDesign neg_lnot_wide.sem := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: unbased unsized literal `'0`/`'1` inside an expression (outside the v1 fragment; allowed as a whole right-hand side)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_fill.sem N) := by
  sv_structure

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → st.boolAt "y" k = if st.boolAt "v" 0 = true then st.boolAt "a" k else st.boolAt "b" k
  known_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [width] ⊢ ↑N + -1 = 0
  [inputsKnown_1] ⊢ ∃ v, st.lookup "v" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (neg_tern_wide.sem N))
    (ha : Acyclic (neg_tern_wide.sem N)) (st : SvState) (heqs : CombEqs (neg_tern_wide.sem N) st)
    (hsh : StateShape (neg_tern_wide.sem N) st) : True := by
  sv_equations?
  trivial

-- (the refusal names the equation fragment; the decidable check's own report is long, so only the
-- failure is pinned)
example (_hc : CombDesign neg_xarm.sem) (_ha : Acyclic neg_xarm.sem) (st : SvState)
    (_heqs : CombEqs neg_xarm.sem st) (_hsh : StateShape neg_xarm.sem st) : True := by
  fail_if_success sv_equations
  trivial

end Examples.«system-verilog».comb_ops.comb_errors
