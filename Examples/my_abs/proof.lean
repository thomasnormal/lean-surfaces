/-
Proof module for `Examples/my_abs/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.my_abs.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication.
-/
import LeanModels

namespace Examples.my_abs.proof

open LeanModels LeanModels.Python

load_program my_abs from "Examples/my_abs/my_abs.json"

/-- Total correctness: `py_prove`'s branch-splitting alternative `split`s
the residual `ite` from the symbolic `if x < 0:` and finishes each side
with `omega` (which understands `natAbs` natively). -/
theorem my_abs_spec (x : PyInt) : my_abs(x) ==> |x| := by
  py_prove [my_abs]

/-- Determinism corollary of `my_abs_spec` — one `py_corollary`
(Surface.lean). -/
theorem my_abs_run_spec (x : Int) {fuel : Nat} {r : Val}
    (h : callFunction my_abs "my_abs" #[.int x] fuel = .ok r) :
    r = .int |x| := by
  py_corollary [my_abs_spec]

end Examples.my_abs.proof
