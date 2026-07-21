/-
Proof module for `Examples/tut_03/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.tut_03.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication.
-/
import LeanModels

namespace Examples.tut_03.proof

open LeanModels LeanModels.Python

load_program tut_03 from "Examples/tut_03/tut_03.json"

/-- Unconditional total correctness: `py_prove` splits the symbolic
branch left by `if x < 0:` and closes both arms with `omega` (which
knows `max`). -/
theorem relu_total (x : PyInt) : tut_03.relu(x) ==> max x 0 := by
  py_prove [tut_03]

/-- With a precondition: the `have` line re-lands `hx` at `Int` for
`py_prove`'s `omega` closer (docs/tutorial/06-when-proofs-fail.md,
failure mode 5). -/
theorem relu_of_nonneg (x : PyInt) (hx : 0 ≤ x) : tut_03.relu(x) ==> x := by
  have hx' : (0 : Int) ≤ x := hx
  py_prove [tut_03]

/-- The same theorem with the proof spelled out, for reading goal states
(docs/tutorial/03-branching-and-preconditions.md walks through each
step's goal). -/
theorem relu_of_nonneg' (x : PyInt) (hx : 0 ≤ x) : tut_03.relu(x) ==> x := by
  have hx' : (0 : Int) ≤ x := hx
  refine ⟨32, ?_⟩
  py_simp [callFunction, tut_03]
  split <;> py_simp
  omega

end Examples.tut_03.proof
