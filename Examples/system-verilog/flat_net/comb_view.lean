import Examples.«system-verilog».flat_net.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on a flat netlist (`Examples/system-verilog/flat_net`, WP-P3b)

A design whose every site is plain (no generate loop) and that has no free parameter: the structure
obligations (reads and windows in range, one driver per bit, rank decreases) are CLOSED statements about
the site list. `sv_structure` decides them (`closeByDecide`, through `LeanModels/Sv/CombViewPlain.lean`)
instead of normalizing them with `simp`, whose cost is quadratic in the number of sites. The visible
difference is that NO goal is left, not even the rank goals `rank[4] < rank[5]`: there is no
`all_goals (intros; omega)` below. (`svgolf/tasks/aes_sbox/reference/sbox_bp.lean` is the 113-gate
instance.)

Build: `lake build Examples.«system-verilog».flat_net.comb_view`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».flat_net.gen

namespace Examples.«system-verilog».flat_net.comb_view

/-- The rank of a site is its depth: `c[0]` 0, then the sum and carry cells of bit `k` at `k + 1`,
`cout` after `c[4]`, and `s[3]`, the last assign of the file, level with `c[4]`. -/
def depth : List Nat := [0, 1, 1, 2, 2, 3, 3, 4, 5, 4]

/-- `CombDesign` alone: no goal left. -/
theorem flat_comb : CombDesign flat_net.sem := by
  sv_structure

/-- The bundle with a `Nat` rank: no goal left. -/
theorem flat_struct : CombDesign flat_net.sem ∧ Acyclic flat_net.sem := by
  sv_structure (rank := rippleRank (fun p => depth.getD p 0) (fun _ _ _ => 0))

/-- `Acyclic` with a lexicographic key (the source position), the one-driver goal supplied by `hc`. -/
theorem flat_acyclic_lex (hc : CombDesign flat_net.sem) : Acyclic flat_net.sem := by
  sv_structure (lexRank := fun
    | .plain p => (p, 0, 0)
    | .fam _ _ _ => (0, 0, 0)) using hc

/-- `Acyclic` with a lexicographic key, alone (the one-driver goal is decided too). -/
theorem flat_acyclic : Acyclic flat_net.sem := by
  sv_structure (lexRank := fun
    | .plain p => (p, 0, 0)
    | .fam _ _ _ => (0, 0, 0))

/-- info: 'Examples.«system-verilog».flat_net.comb_view.flat_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_comb

/-- info: 'Examples.«system-verilog».flat_net.comb_view.flat_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_struct

/-- info: 'Examples.«system-verilog».flat_net.comb_view.flat_acyclic_lex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_acyclic_lex

/-- info: 'Examples.«system-verilog».flat_net.comb_view.flat_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_acyclic

/-! ## Negative: a wrong rank is still REJECTED, with the site that violates it (the sampling stage,
which runs before the proof, is unchanged) -/

/--
error: sv_structure: the rank does not decrease along a read: `plain#1` (rank 0) reads a window of `c` driven by `plain#0` (rank 0, window c[0]); a driver must have a SMALLER rank than its reader (sampled at [] = []; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
-/
#guard_msgs (whitespace := lax) in
theorem flat_bad_rank : Acyclic flat_net.sem := by
  sv_structure (rank := fun _ => 0)

end Examples.«system-verilog».flat_net.comb_view
