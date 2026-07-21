/-
Examples/tut_03 — three-file example layout (see Examples/tri/spec.lean
for the pattern rationale): tut_03.py (pure Python), tut_03.json
(generated envelope), THIS FILE (checks + statements, `:= by proofs`),
proof.lean (the real proofs, namespace `Examples.tut_03.proof`).
Tutorial 03 (docs/tutorial/03-branching-and-preconditions.md) companion.
-/
import Examples.tut_03.proof

open LeanModels LeanModels.Python

load_program tut_03 from "Examples/tut_03/tut_03.json"

/-! Tutorial 03 (docs/tutorial/03-branching-and-preconditions.md):
hypotheses as preconditions, branching, and reading goal states. -/
#py_check tut_03.relu(5) = 5
#py_check tut_03.relu(-5) = 0
#py_check tut_03.relu(0) = 0

/-- Unconditional total correctness: `py_prove` splits the symbolic
branch left by `if x < 0:` and closes both arms with `omega` (which
knows `max`). -/
theorem relu_total (x : PyInt) : tut_03.relu(x) ==> max x 0 := by proofs

/-- With a precondition, the spec simplifies: on nonnegative inputs
`relu` is the identity. A precondition is an ordinary named hypothesis —
but `py_prove` (unlike `py_begin`) does not restate `Py*`-branded
hypotheses for `omega`, so the proof re-lands `hx` at `Int` first
(docs/tutorial/06-when-proofs-fail.md, failure mode 5). -/
theorem relu_of_nonneg (x : PyInt) (hx : 0 ≤ x) : tut_03.relu(x) ==> x := by proofs

/-- The same theorem with the proof spelled out, for reading goal states
(docs/tutorial/03-branching-and-preconditions.md walks through each
step's goal — see `Examples/tut_03/proof.lean`). -/
theorem relu_of_nonneg' (x : PyInt) (hx : 0 ≤ x) : tut_03.relu(x) ==> x := by proofs

/-! Delaborator regression (LeanModels/Python/Delab.lean): statements
print back in surface notation. -/

/-- info: relu_total (x : PyInt) : tut_03.relu(x) ==> max x 0 -/
#guard_msgs in
#check relu_total
