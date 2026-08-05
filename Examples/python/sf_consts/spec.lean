/-
Examples/python/sf_consts — three-file example layout. The G1
(module-level constants) acceptance example: sunfish.py's actual constant
block — board corners `A1, H1, A8, H8 = 91, 98, 21, 28` (a top-level
tuple-unpack), compass directions, and the mate score — referenced from
function bodies. Before G1 these constants had to be inlined by hand into
every transliteration (sf_bound_rec's literal -69290); now the interpreter
resolves them from the module source itself.

`MATE_UPPER = 69290` carries the sunfish VALUE but not yet its defining
expression `piece["K"] + 10 * piece["Q"]` — dict-derived, waiting on the
dict tier (G2/step 3 of the sunfish ladder).
-/
import Examples.python.sf_consts.proof

open LeanModels LeanModels.Python

load_program sf_consts from "Examples/python/sf_consts/sf_consts.json"

/-! Non-vacuity: concrete runs (values cross-checked against CPython). -/
#py_check sf_consts.rotate_sq(91) = 28
#py_check sf_consts.rotate_sq(28) = 91
#py_check sf_consts.corners_sum() = 238
#py_check sf_consts.is_back_rank_white(25) = true
#py_check sf_consts.is_back_rank_white(91) = false
#py_check sf_consts.loss() = -69290

/-- `rotate`'s square map is the 120-board point reflection. -/
theorem rotate_sq_spec (i : PyInt) :
    sf_consts.rotate_sq(i) ==> 119 - i := by proofs

/-- The four corner constants resolve from the top-level tuple-unpack. -/
theorem corners_sum_spec : sf_consts.corners_sum() ==> (238 : PyInt) := by proofs

/-- `-MATE_UPPER`, resolved from the module constant, is sunfish's loss
score. -/
theorem loss_spec : sf_consts.loss() ==> (-69290 : PyInt) := by proofs

/-- The promotion-rank test, against the mathematical form. -/
theorem is_back_rank_white_spec (i : PyInt) :
    sf_consts.is_back_rank_white(i) ==> decide (21 ≤ i ∧ i ≤ 28) := by proofs
