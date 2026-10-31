import Examples.«system-verilog».comb_proc.comb_view
import LeanModels.Sv.CombProcTactic

/-!
# `always_comb` refusals: the tactic message names the site and the reason

Each negative design is a copy of the `add_proc` carry cell with ONE defect; each is refused by
`sv_structure` with a tactic error (never an elaboration error of the kernel), the first line of which is the
message the checker's `--tactics` advisory reports as `in_fragment false`:

* `neg_case`: a `case` statement (outside the first fragment);
* `neg_latch`: an `if` without `else` (the carry is not assigned on every path: a latch);
* `neg_multi`: a second statement in the block (two written windows in one body);
* `neg_selfaff`: the body reads `c[N - i]` while writing `c[i + 1]`: not the same access syntactically, so it
  passes the recognizer, and the obligation `noSelfRead` fails at the sampled point `N = 1` (the same window);
* `neg_condx` is accepted by `sv_structure` and fails later, at the equations stage: the condition reads `u[i]`,
  which nothing drives, so the `cover` obligation of `sv_equations` has no proof (see `comb_hint.lean` for the
  shape of those goals).

The two designs that read the window they write VERBATIM (`c[i+1] = c[i+1] ^ a[i]`) or that write through a
run-time index never get this far: `load_design_sv2` itself refuses them (the `always_comb` self-read guard of
`CombGuard2`, and the dynamic target), with the loader's message.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».comb_proc.comb_errors

load_design_sv2 neg_case from "Examples/system-verilog/comb_proc/neg/neg_case.sv.json"
load_design_sv2 neg_latch from "Examples/system-verilog/comb_proc/neg/neg_latch.sv.json"
load_design_sv2 neg_multi from "Examples/system-verilog/comb_proc/neg/neg_multi.sv.json"
load_design_sv2 neg_selfaff from "Examples/system-verilog/comb_proc/neg/neg_selfaff.sv.json"

/--
error: sv_structure: outside the supported fragment — site `g_bit#1`: always_comb statement `case` (outside the first fragment)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (neg_case.sem N).lowerComb = some d' ∧ CombDesign d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `g_bit#1`: always_comb does not assign its target on every path (an `if` without `else` is a latch)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (neg_latch.sem N).lowerComb = some d' ∧ CombDesign d' := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `g_bit#1`: always_comb block with several statements (outside the first fragment: write one if/else tree that assigns the target on every path)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (neg_multi.sem N).lowerComb = some d' ∧ CombDesign d' := by
  sv_structure

/--
error: sv_structure: noSelfRead obligation fails — `g_bit#1[0]` reads c[1], which overlaps the window it writes (c[1]): an `always_comb` body may not read what it writes (sampled at [N] = [1]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (neg_selfaff.sem N).lowerComb = some d' ∧ CombDesign d' := by
  sv_structure

/-! ## A refusal can never be proved: the error is logged and the goal admitted

The new elaborators do not throw on a refusal (the framework would then fall through to the original
elaborator and report ITS generic message): they log the error and admit the goal. The file therefore
fails to compile (the error above), and the theorem depends on `sorryAx`, so the checker's axiom check refuses
it a second time. Pinned: the error, then the axioms of the declaration the error leaves behind. -/

/--
error: sv_structure: outside the supported fragment — site `g_bit#1`: always_comb statement `case` (outside the first fragment)
-/
#guard_msgs (whitespace := lax) in
theorem neg_case_refused (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (neg_case.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
    (fun _ pos i => if pos = 0 then 0 else i.toNat + 1))
  all_goals (intros; omega)

/-- info: 'Examples.«system-verilog».comb_proc.comb_errors.neg_case_refused' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neg_case_refused

end Examples.«system-verilog».comb_proc.comb_errors
