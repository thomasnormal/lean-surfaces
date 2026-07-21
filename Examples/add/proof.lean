/-
Proof module for `Examples/add/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.add.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication.
-/
import LeanModels

namespace Examples.add.proof

open LeanModels LeanModels.Python

load_program add from "Examples/add/add.json"

/-- Total correctness: straight-line body, one `py_prove`. -/
theorem add_total (a b : PyInt) : add(a, b) ==> a + b := by
  py_prove [add]

/-- Determinism corollary of `add_total` — one `py_corollary`
(Surface.lean). -/
theorem add_spec (a b : Int) {fuel : Nat} {r : Val}
    (h : callFunction add "add" #[.int a, .int b] fuel = .ok r) :
    r = .int (a + b) := by
  py_corollary [add_total]

/-- The strengthened partial arrow, free from `add_total` via
`CallsTo.partialTo` (determinism modulo fuel). -/
theorem add_partial (a b : PyInt) : add(a, b) ~~> a + b := by
  py_corollary [add_total]

end Examples.add.proof
