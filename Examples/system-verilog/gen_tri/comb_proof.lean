import Examples.«system-verilog».gen_tri.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on generate bounds that name an enclosing genvar (`Examples/system-verilog/gen_tri`)

Row `i` of `t` is written by the loop `g_lo` (`j < i + 1`, the cells on and below the diagonal) and the loop `g_hi`
(`j < N - 1 - i`, the cells above it); `y[i]` reads the diagonal cell. The obligations quantify each inner index under
its row (`∀ i, 0 ≤ i → i < N → ∀ j, 0 ≤ j → j < i + 1 → …`), the cells of `t` are row-major offsets (`sv_rowmajor`),
and `omega` closes what is left. `N` is an `int` parameter: the range premise `hR` keeps it one. The generate fuel of an inner loop is owed at every row (`∀ i < N, (i + 1).toNat ≤ …`),
closed by the tactic itself.

Build: `lake build Examples.«system-verilog».gen_tri.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_tri.gen

namespace Examples.«system-verilog».gen_tri.comb_proof

/-- The structure of `gen_tri`, at every `N`: one driver per bit, every window in range. -/
theorem gen_tri_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) : CombDesign (gen_tri.sem N) := by
  sv_structure
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

/-- The rank: the cells first, the diagonal reads (`y`, the third item of the row body) after them. -/
theorem gen_tri_acyclic (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) : Acyclic (gen_tri.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_row" 2 [_] => (1, 0, 0)
    | _ => (0, 0, 0))
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

/--
info: 'Examples.«system-verilog».gen_tri.comb_proof.gen_tri_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_tri_comb

/--
info: 'Examples.«system-verilog».gen_tri.comb_proof.gen_tri_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_tri_acyclic

end Examples.«system-verilog».gen_tri.comb_proof
