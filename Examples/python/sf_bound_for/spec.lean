/-
Examples/python/sf_bound_for — three-file example layout. THE STEP-2
MILESTONE of the sunfish ladder: sunfish.py's fail-soft beta-cutoff loop
in near-verbatim form —

    best = -MATE_UPPER            # G1 module constant
    for score in scores:          # step-2 `for` (was: index while-loop)
        best = max(best, score)   # B1 builtin  (was: if/else)
        if best >= gamma:
            break
    return best

— proved to compute exactly `sfSearchMoves`, the verbatim copy of
`searchMoves` from sunfish's hand-written formal tree
(formal/Sunfish/Bound.lean), shared with Examples/python/sf_bound_rec.
The SOLE remaining transliteration between this and the shipped
`Searcher.bound` loop is precomputing the generator `moves()` into the
list `scores` (generators are the last ladder step).

Non-vacuity gap (recorded per AGENTS.md): `harness/cases.json` rows are
inexpressible — `leanmodels-run` parses CLI args as ints only and
`scores` is a list. Fallback: the runs below were cross-checked against
CPython by executing sf_bound_for.py directly (2026-08-06).
-/
import Examples.python.sf_bound_for.proof

open LeanModels LeanModels.Python

load_program sf_bound_for from "Examples/python/sf_bound_for/sf_bound_for.json"

/-! Non-vacuity: concrete runs (values cross-checked against CPython). -/
#py_check sf_bound_for.bound_loop(([] : List Int), 5) = -69290
#py_check sf_bound_for.bound_loop([3, 1, 2], 10) = 3
#py_check sf_bound_for.bound_loop([3, 1, 2], 2) = 3
#py_check sf_bound_for.bound_loop([-5, 7, 100], 7) = 7
#py_check sf_bound_for.bound_loop([1, 2, 3], -70000) = 1
#py_check sf_bound_for.bound_loop([-70000, -5], -69290) = -69290

/-- **Total correctness**: the near-verbatim sunfish cutoff loop computes
`formal/Sunfish/Bound.lean`'s `searchMoves gamma · scores LOSS`. -/
theorem bound_loop_total (scores : List PyInt) (gamma : PyInt) :
    sf_bound_for.bound_loop(scores, gamma) ==>
      sfSearchMoves gamma scores (-69290) := by proofs
