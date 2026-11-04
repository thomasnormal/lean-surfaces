import Examples.«system-verilog».comb_ovr.gen
import LeanModels.Sv.CombProcTactic

/-!
# What stays outside the default-then-override fragment, and the message (WP-G S3b)

Each negative design has ONE defect; each is refused with a tactic message that names the site:

* `neg_rbw`: the override READS the window it writes (`y = y ^ b`): the read-before-write that SSA substitution
  would cover is NOT covered (the summary's `noSelfRead` and the early `selfReadSyntactic` refuse every read of
  the written window);
* `neg_interleave`: a window written in two separate groups of statements (`y = a; z = b; if (e) y = b;`: the
  statements of one window must be together, S1b gate b);
* `neg_otherwindow`: an override that writes ANOTHER window of the signal (a latch for that window);
* `neg_second`: a second UNCONDITIONAL assignment of the target (only `if (c) …;` overrides can follow);
* `neg_elsechain`: an `if … else` after the first statement;
* `neg_nested`: a `begin … end` with several statements as a statement of a block;
* `neg_latch`: no default before the override (an `if` without `else` alone is a latch);
* `case_tree`: a `case` whose arms are trees (follow-up: arms that are `if` trees or blocks).
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_ovr.comb_errors

load_design_sv2 neg_rbw from "Examples/system-verilog/comb_ovr/neg/neg_rbw.sv.json"
load_design_sv2 neg_interleave from "Examples/system-verilog/comb_ovr/neg/neg_interleave.sv.json"
load_design_sv2 neg_otherwindow from "Examples/system-verilog/comb_ovr/neg/neg_otherwindow.sv.json"
load_design_sv2 neg_second from "Examples/system-verilog/comb_ovr/neg/neg_second.sv.json"
load_design_sv2 neg_elsechain from "Examples/system-verilog/comb_ovr/neg/neg_elsechain.sv.json"
load_design_sv2 neg_nested from "Examples/system-verilog/comb_ovr/neg/neg_nested.sv.json"
load_design_sv2 neg_latch from "Examples/system-verilog/comb_ovr/neg/neg_latch.sv.json"
load_design_sv2 case_tree from "Examples/system-verilog/comb_ovr/case_tree.sv.json"

/--
error: sv_structure: outside the supported fragment — site `plain#0`: always_comb reads the window it writes (`y`)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_rbw.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: an always_comb body writes a window in two separate groups of statements (outside the second fragment: put the statements of one window together)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_interleave.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: always_comb writes more than one window (the first fragment has one written window per process: split it into one always_comb per target)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_otherwindow.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a second unconditional assignment of the target in an always_comb block (outside the second fragment: only `if (c) …;` overrides can follow the first statement)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_second.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: an `if … else` after the first statement of an always_comb block (outside the second fragment: only `if (c) …;` without `else` can follow, as a default-then-override body)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_elsechain.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: a `begin … end` with several statements as a statement of a block (outside the second fragment: write its statements in the outer block)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_nested.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: always_comb does not assign its target on every path (an `if` without `else` is a latch)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', neg_latch.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `plain#0`: `case` arm is not a single assignment `t = v;` (the first fragment has no `begin … end`, `if` or `case` inside an arm)
-/
#guard_msgs (whitespace := lax) in
example : ∃ d', case_tree.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure

end Examples.«system-verilog».comb_ovr.comb_errors
