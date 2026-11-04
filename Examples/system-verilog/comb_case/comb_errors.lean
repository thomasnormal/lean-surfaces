import Examples.«system-verilog».comb_case.gen
import LeanModels.Sv.CombProcTactic

/-!
# What stays outside the `case` fragment, and the message (WP-G S3a)

Each negative design has ONE defect; each is refused with a tactic message that names the site (the first
line is what the checker's `--tactics` advisory reports as `in_fragment false`):

* `neg_nodefault`: no `default`: the statement does not assign its target on every path (a latch);
* `neg_unsized`: an unsized item (`1:`) is 32 bits wide, so the subject is zero-extended to it: a width conversion;
* `neg_width`: an item wider than the subject (`3'd1:` on a 2-bit subject): a width conversion;
* `neg_block`: an arm in `begin … end`: an arm must be one assignment;
* `neg_nested`: an `if` inside an arm: an arm must be one assignment (a follow-up);
* `neg_two_targets`: the arms write different targets (`y` and `z`): one written window per process;
* `neg_inside`: `case … inside` (wildcard matching) is outside the fragment;

An item with an `x`/`z` bit (`neg_xitem`: `2'b1x:`) is accepted by the recognizer and refused at the equations
stage: the right-hand side is outside the equation fragment (its literals must be known). `unique`, `priority`,
`casez` and `casex` never reach the tactics (the extractor does not model them, and the source gate refuses
`unique`/`priority`).
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_case.comb_errors

load_design_sv2 neg_nodefault from "Examples/system-verilog/comb_case/neg/neg_nodefault.sv.json"
load_design_sv2 neg_unsized from "Examples/system-verilog/comb_case/neg/neg_unsized.sv.json"
load_design_sv2 neg_width from "Examples/system-verilog/comb_case/neg/neg_width.sv.json"
load_design_sv2 neg_block from "Examples/system-verilog/comb_case/neg/neg_block.sv.json"
load_design_sv2 neg_nested from "Examples/system-verilog/comb_case/neg/neg_nested.sv.json"
load_design_sv2 neg_two_targets from "Examples/system-verilog/comb_case/neg/neg_two_targets.sv.json"
load_design_sv2 neg_inside from "Examples/system-verilog/comb_case/neg/neg_inside.sv.json"
load_design_sv2 neg_xitem from "Examples/system-verilog/comb_case/neg/neg_xitem.sv.json"

/--
error: sv_structure: outside the supported fragment — site `plain#0`: always_comb `case` has no `default`: it does not assign its target on every path (a latch)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_nodefault.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: width conversion (an operand is not as wide as its context at the default parameters, so slang inserted an implicit zero-extension or truncation; the v1 fragment needs every operand exactly as wide as its target: widen or narrow it explicitly)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_unsized.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: width conversion (an operand is not as wide as its context at the default parameters, so slang inserted an implicit zero-extension or truncation; the v1 fragment needs every operand exactly as wide as its target: widen or narrow it explicitly)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_width.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: `case` arm is not a single assignment `t = v;` (the first fragment has no `begin … end`, `if` or `case` inside an arm)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_block.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: `case` arm is not a single assignment `t = v;` (the first fragment has no `begin … end`, `if` or `case` inside an arm)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_nested.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: always_comb writes more than one window (the first fragment has one written window per process: split it into one always_comb per target)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_two_targets.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: always_comb statement `case … inside` (outside the first fragment)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_inside.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

-- the x-item design is accepted by the recognizer; the refusal is at the equations stage and names the
-- equation fragment (the decidable check's own report after the first line is long, so only a substring
-- of the message is pinned)
/--
error: sv_equations: a right-hand side is outside the fragment of `sv_equations` (an expression over accesses and known literals built from `& | ^`, `~ !`, t
-/
#guard_msgs (error, substring := true, whitespace := lax) in
example {d' : Design2} (_hl : neg_xitem.sem.lowerComb = some d') (_hc : CombDesign d') (_ha : Acyclic d')
    (st : SvState) (_heqs : CombEqs d' st) (_hsh : StateShape d' st) : True := by
  sv_equations
  all_goals sorry

end Examples.«system-verilog».comb_case.comb_errors
