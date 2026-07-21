/-
Proof module for `Examples/arith/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.arith.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication.
-/
import LeanModels

namespace Examples.arith.proof

open LeanModels LeanModels.Python

load_program arith from "Examples/arith/arith.json"

/-- `floordiv(a, 0)` raises `ZeroDivisionError` for every `a`: the error
path is loop-free, so `py_prove` closes it. -/
theorem floordiv_zero (a : PyInt) : arith.floordiv(a, 0) ==>! .zeroDivisionError := by
  py_prove [arith]

/-- Same shape for `%`: `mod(a, 0)` raises for every `a`. -/
theorem mod_zero (a : PyInt) : arith.mod(a, 0) ==>! .zeroDivisionError := by
  py_prove [arith]

end Examples.arith.proof
