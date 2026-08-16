/-
Real proofs for Examples/python/sf_bound_for/spec.lean.

THE STEP-2 MILESTONE: sunfish.py's fail-soft cutoff loop in near-verbatim
form — `best = -MATE_UPPER` (G1 module constant), `for score in scores:`
(step-2 `for`), `best = max(best, score)` (B1 builtin), the beta-cutoff
`break` — proved to compute exactly `sfSearchMoves`, the verbatim copy of
`searchMoves` from sunfish's hand-written formal tree
(formal/Sunfish/Bound.lean), IMPORTED from sf_bound_rec: the index-
recursion form and this `for` form are certified against the SAME model
constant.

Proof shape: `execFor` is a frozen recursion point (like `execWhile`) —
unfold exactly one step with `rw [execFor.eq_2/eq_3]`, never via the simp
set. `key` is a list induction over it in fuel-threshold form
(`execFor_mono` generalizes each concrete-fuel run), stated at the
uniform post-first-iteration environment shape (`score` bound). The main
theorem unrolls the first iteration by hand — the target variable is
CREATED by it, so the environment grows mid-loop (the F-2 shape) — and
splices `key` for the tail.
-/
import Examples.python.sf_bound_rec.proof

namespace Examples.python.sf_bound_for.proof

open LeanModels LeanModels.Python

load_program sf_bound_for from "Examples/python/sf_bound_for/sf_bound_for.json"

/-- **Total correctness**: the near-verbatim sunfish cutoff loop computes
`formal/Sunfish/Bound.lean`'s `searchMoves gamma · scores LOSS`.

The invariant is the standard fold-in-progress one — what is still to be
scanned, folded onto the running `best`, is what the whole scan computes —
and the `exit` clause is what a `break` needs: at the cutoff the answer is
`best` itself, established at the break site from the branch fact. -/
theorem bound_loop_total (scores : List PyInt) (gamma : PyInt) :
    sf_bound_for.bound_loop(scores, gamma) ==>
      sfSearchMoves gamma scores (-69290) := by
  py_vcgen [sf_bound_for]
    (inv := fun (rest : List Int) (best : Int) =>
      sfSearchMoves gamma scores (-69290) = sfSearchMoves gamma rest best)
    (exit := fun (best : Int) =>
      sfSearchMoves gamma scores (-69290) = best)
  all_goals grind [sfSearchMoves]

end Examples.python.sf_bound_for.proof
