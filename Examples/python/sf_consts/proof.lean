/-
Real proofs for Examples/python/sf_consts/spec.lean — the G1
(module-level constants) acceptance example: sunfish.py's actual constant
block (board corners, compass directions, mate score), referenced from
function bodies and resolved by the interpreter's module-globals pass.
-/
import LeanModels

namespace Examples.python.sf_consts.proof

open LeanModels LeanModels.Python

load_program sf_consts from "Examples/python/sf_consts/sf_consts.json"

theorem rotate_sq_spec (i : PyInt) :
    sf_consts.rotate_sq(i) ==> 119 - i := by
  py_prove [sf_consts]

theorem corners_sum_spec : sf_consts.corners_sum() ==> (238 : PyInt) := by
  py_prove [sf_consts]

theorem loss_spec : sf_consts.loss() ==> (-69290 : PyInt) := by
  py_prove [sf_consts]

/-- The promotion-rank test, against the mathematical form: `and` on two
comparisons returns the deciding operand (CPython truthiness), which here
is always a bool. -/
theorem is_back_rank_white_spec (i : PyInt) :
    sf_consts.is_back_rank_white(i) ==> decide (21 ≤ i ∧ i ≤ 28) := by
  refine ⟨32, ?_⟩
  by_cases h1 : (21 : Int) ≤ i <;> by_cases h2 : (i : Int) ≤ 28 <;>
    py_simp [callFunction, callIn, sf_consts, h1, h2] <;> grind

end Examples.python.sf_consts.proof
