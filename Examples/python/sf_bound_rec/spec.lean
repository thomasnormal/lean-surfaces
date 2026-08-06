/-
Examples/python/sf_bound_rec — three-file example layout. The fail-soft
best loop with beta cutoff from sunfish.py's `Searcher.bound` (the sunfish
chess engine), as index-carrying recursion, proved to compute EXACTLY the
`searchMoves` model that sunfish's hand-written formal tree
(formal/Sunfish/Bound.lean) reasons about. The point: the Python-to-Lean
transcription step that sunfish's formal/ audit does by hand (8 divergences
found in one manual audit) is machine-checked here for this fragment.

Differential rows: harness/cases.json carries typed-JSON argument
rows for this function (leanmodels-run accepts the canonical
{"t":…,"v":…} encoding for list/tuple arguments); the runs below
are additionally checked at elaboration time.
-/
import Examples.python.sf_bound_rec.proof

open LeanModels LeanModels.Python

load_program sf_bound_rec from "Examples/python/sf_bound_rec/sf_bound_rec.json"

/-! Non-vacuity: concrete runs (values cross-checked against CPython).
`-69290 = -MATE_UPPER`, the sunfish loss score. -/
#py_check sf_bound_rec.bound_rec(([] : List Int), 5, 0, -69290) = -69290
#py_check sf_bound_rec.bound_rec([3, 1, 2], 10, 0, -69290) = 3
#py_check sf_bound_rec.bound_rec([3, 1, 2], 2, 0, -69290) = 3
#py_check sf_bound_rec.bound_rec([-5, 7, 100], 7, 0, -69290) = 7
#py_check sf_bound_rec.bound_rec([1, 2, 3], -70000, 0, -69290) = 1
#py_check sf_bound_rec.bound_rec([5, 9, 4], 8, 1, 3) = 9

/-- **Total correctness** of the general index-carrying form: from index
`i`, the run returns `sfSearchMoves gamma (scores.drop i.toNat) best` —
the verbatim `formal/Sunfish/Bound.lean` `searchMoves`, score callback
pre-applied (defined in proof.lean at root namespace, fib's rationale). -/
theorem bound_rec_total (scores : List PyInt) (gamma i best : PyInt)
    (hi : 0 ≤ i) :
    sf_bound_rec.bound_rec(scores, gamma, i, best) ==>
      sfSearchMoves gamma (scores.drop i.toNat) best := by proofs

/-- The headline form: from the top of the move loop
(`i = 0`, `best = -MATE_UPPER = -69290`), the Python recursion computes
exactly `formal/Sunfish/Bound.lean`'s `searchMoves gamma · scores LOSS`. -/
theorem bound_rec_search (scores : List PyInt) (gamma : PyInt) :
    sf_bound_rec.bound_rec(scores, gamma, 0, -69290) ==>
      sfSearchMoves gamma scores (-69290) := by proofs
