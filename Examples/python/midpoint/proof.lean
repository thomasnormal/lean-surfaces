/-
Proof module for `Examples/python/midpoint/spec.lean` (three-file example
layout). Every theorem stated in spec.lean is proved here under the same
name; the spec side is `:= by proofs`, which resolves
`Examples.python.midpoint.proof.<decl>` (Surface.lean). Statements are duplicated
between the two files BY DESIGN (Lean has no forward declarations); the
spec-side `:= by proofs` reference typechecks the duplication.
-/
import LeanModels

namespace Examples.python.midpoint.proof

open LeanModels LeanModels.Python

load_program midpoint from "Examples/python/midpoint/midpoint.json"

/-- Total correctness: straight-line body, one `py_prove` (`py_simp`
reduces `evalBinOp .floorDiv` to `Int.fdiv` and discharges the `2 = 0`
divisor guard). -/
theorem midpoint_spec (a b : PyInt) : midpoint(a, b) ==> Int.fdiv (a + b) 2 := by
  py_prove [midpoint]

set_option linter.unusedVariables false in
/-- The `/` form, derived from `midpoint_spec` by the value bridge
`Int.fdiv_eq_ediv_of_nonneg` — NOT by re-executing the body (rationale for
the not-load-bearing `ha`/`hb`: `Examples/python/midpoint/spec.lean`). -/
theorem midpoint_nonneg (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    midpoint(a, b) ==> (a + b) / 2 := by
  py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]

/-- Determinism corollary of `midpoint_spec` — one `py_corollary`
(Surface.lean). -/
theorem midpoint_run_spec (a b : Int) {fuel : Nat} {r : Val}
    (h : callFunction midpoint "midpoint" #[.int a, .int b] fuel = .ok r) :
    r = .int (Int.fdiv (a + b) 2) := by
  py_corollary [midpoint_spec]

end Examples.python.midpoint.proof
