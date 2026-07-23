/-
Proof module for `Examples/python/tut_02/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.python.tut_02.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication.
-/
import LeanModels

namespace Examples.python.tut_02.proof

open LeanModels LeanModels.Python

load_program tut_02 from "Examples/python/tut_02/tut_02.json"

/-- Total correctness: straight-line body, one `py_prove`. -/
theorem square_total (x : PyInt) : tut_02.square(x) ==> x * x := by
  py_prove [tut_02]

/-- The relational reading, via the hypothesis-position arrow `⇓` and
determinism-modulo-fuel (`CallsTo.typed_int_eq`, Surface.lean). -/
theorem square_result (x r : PyInt) (h : tut_02.square(x) ⇓ r) : r = x * x :=
  CallsTo.typed_int_eq h (square_total x)

/-- Squares are nonnegative — once `square_result` pins the result, the
rest is ordinary mathematics with ordinary Lean tools. -/
theorem square_nonneg (x r : PyInt) (h : tut_02.square(x) ⇓ r) : 0 ≤ r := by
  rw [square_result x r h]
  rcases Int.le_total 0 x with hx | hx
  · exact Int.mul_nonneg hx hx
  · have := Int.mul_nonneg (a := -x) (b := -x) (by omega) (by omega)
    rwa [Int.neg_mul_neg] at this

end Examples.python.tut_02.proof
