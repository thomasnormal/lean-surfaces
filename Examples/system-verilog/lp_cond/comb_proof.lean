import Examples.«system-verilog».lp_cond.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on localparams defined by comparisons and `?:` (`Examples/system-verilog/lp_cond`)

`S = ((N > 2) ? 1 : 0) + ((N >= 5) ? 1 : 0)` is a declared dimension (`g[S:0]`), a generate bound and an index
(`g[S][i]`); `W = (N < 4) ? 4 : N` is a width and a bound. At a symbolic `N` the parameter stage cannot decide the
conditions: it evaluates both arms of each `?:` and the environment holds the `if` (`liftIte`), which the summary's value
of the definition also is (`CE.eval`); the obligations hold the same `if`s, and `omega` splits them (the cells of `g` are row-major offsets,
`sv_rowmajor`, as for every 2-D array). The range premise
keeps every value an `int` (`N < 2147483647`, as for `lp_add`).

Build: `lake build Examples.«system-verilog».lp_cond.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».lp_cond.gen

namespace Examples.«system-verilog».lp_cond.comb_proof

/-- The structure of `lp_cond`, at every `N`: one driver per bit, every window in range. -/
theorem lp_cond_comb (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (lp_cond.sem N) := by
  sv_structure
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

/-- The rank: the input stage 0, stage `k` at `k + 1`, the outputs above the last stage (`S ≤ 2`). -/
theorem lp_cond_acyclic (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : Acyclic (lp_cond.sem N) := by
  sv_structure (lexRank := fun
    | .plain _ => (1, 0, 0)
    | .fam "g_node" 0 [k, _] => (k.toNat + 1, 0, 0)
    | .fam "g_out" 0 [_] => (3, 0, 0)
    | _ => (0, 0, 0))
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

/--
info: 'Examples.«system-verilog».lp_cond.comb_proof.lp_cond_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lp_cond_comb

/--
info: 'Examples.«system-verilog».lp_cond.comb_proof.lp_cond_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lp_cond_acyclic

end Examples.«system-verilog».lp_cond.comb_proof
