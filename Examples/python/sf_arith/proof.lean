/-
Real proofs for Examples/python/sf_arith/spec.lean.
-/
import LeanModels

open LeanModels LeanModels.Python

namespace Examples.python.sf_arith.proof

load_program sf_arith from "Examples/python/sf_arith/sf_arith.json"

theorem child_score_spec (s v : PyInt) :
    sf_arith.child_score(s, v) ==> -(s + v) := by
  py_prove [sf_arith]

theorem futility_code (s v g : PyInt) :
    sf_arith.futility_margin(s, v, g) ==>
      (if s + v < g then (1 : Int) else 0) := by
  py_prove [sf_arith]

theorem futility_comment_true (s v g : PyInt) :
    sf_arith.futility_margin(s, v, g) ==>
      (if 1 - g ≤ -(s + v) then (1 : Int) else 0) := by
  py_prove [sf_arith]

/-- The `and`-chain condition is three branch points — outside `py_prove`'s
single-`split` recipe — so the branches are decided up front
(ag_clamp01 pattern, AGENTS.md failure table). -/
theorem lmr_spec (d i v : PyInt) :
    sf_arith.lmr_amount(d, i, v) ==>
      (if 4 ≤ d ∧ 8 ≤ i ∧ v < 0 then (1 : Int) else 0) := by
  refine ⟨32, ?_⟩
  by_cases h1 : 4 ≤ d <;> by_cases h2 : 8 ≤ i <;> by_cases h3 : v < 0 <;>
    py_simp [callFunction, sf_arith, h1, h2, h3] <;> grind

end Examples.python.sf_arith.proof
