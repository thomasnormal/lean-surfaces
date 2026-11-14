import Examples.«system-verilog».gen_deep.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on generate loops nested three deep (`Examples/system-verilog/gen_deep`)

The obligations quantify each site's indices outermost first (`∀ i, 0 ≤ i → i < N → ∀ j, … → ∀ k, …`), an inner bound
read at the valuation of the loops around it (`k < i + j`); the cells of the 2-D arrays are row-major offsets
(`sv_rowmajor`), and `omega` closes what is left.

Build: `lake build Examples.«system-verilog».gen_deep.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_deep.gen

namespace Examples.«system-verilog».gen_deep.comb_proof

/-- The structure of `gen_deep`, at every `N`: one driver per bit, every window in range. -/
theorem gen_deep_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) : CombDesign (gen_deep.sem N) := by
  sv_structure
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

/-- The rank: the copies in `t` first, then the ANDs `d` (`g_col`, position 1), then `y` (`g_row`, position 1). -/
theorem gen_deep_acyclic (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) : Acyclic (gen_deep.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_col" 1 [_, _] => (1, 0, 0)
    | .fam "g_row" 1 [_] => (2, 0, 0)
    | _ => (0, 0, 0))
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

/--
info: 'Examples.«system-verilog».gen_deep.comb_proof.gen_deep_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_deep_comb

/--
info: 'Examples.«system-verilog».gen_deep.comb_proof.gen_deep_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_deep_acyclic

end Examples.«system-verilog».gen_deep.comb_proof
