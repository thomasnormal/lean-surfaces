import Examples.«system-verilog».gen_if.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on conditional generate constructs inside generate loops (`Examples/system-verilog/gen_if`)

Each site of an arm is owed its obligations where its guard selects it: the in-range goal of `b[i - 1]` has `1 ≤ i` as a
hypothesis, the two arms of `g_node` write the same cell `g[l+1][i]` under complementary guards (`l + 1 ≤ i` and
`¬ l + 1 ≤ i`), so their one-driver goal is vacuous, and the `else if` arm reads `g[3][i - 1]` under `¬ i = 0`. The
condition's operands are evaluated at the signed 32-bit type, so their values are owed in that range (`hR`).

Build: `lake build Examples.«system-verilog».gen_if.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_if.gen

namespace Examples.«system-verilog».gen_if.comb_proof

/-- The structure of `gen_if`, at every `N`: one driver per bit, every window in range. -/
theorem gen_if_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (gen_if.sem N) := by
  sv_structure
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

/-- The rank: the inputs' level 0 first, level `l + 1` after level `l` (both arms), the outputs last. -/
theorem gen_if_acyclic (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : Acyclic (gen_if.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_node" _ [l, _] => (l.toNat + 1, 0, 0)
    | .fam "g_out" _ [_] => (5, 0, 0)
    | _ => (0, 0, 0))
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

/--
info: 'Examples.«system-verilog».gen_if.comb_proof.gen_if_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_if_comb

/--
info: 'Examples.«system-verilog».gen_if.comb_proof.gen_if_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_if_acyclic

end Examples.«system-verilog».gen_if.comb_proof
