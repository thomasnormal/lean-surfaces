/-
Examples/python/tut_02 — three-file example layout (see Examples/python/tri/spec.lean
for the pattern rationale): tut_02.py (pure Python), tut_02.json
(generated envelope), THIS FILE (checks + statements, `:= by proofs`),
proof.lean (the real proofs, namespace `Examples.python.tut_02.proof`).
Tutorial 02 (docs/tutorial/02-first-spec.md) companion.
-/
import Examples.python.tut_02.proof

open LeanModels LeanModels.Python

load_program tut_02 from "Examples/python/tut_02/tut_02.json"

/-! Tutorial 02 (docs/tutorial/02-first-spec.md): the `==>` arrow and
`py_prove` on straight-line code. -/
#py_check tut_02.square(5) = 25
#py_check tut_02.square(-4) = 16
#py_check tut_02.square(0) = 0

/-- Total correctness: `square(x)` terminates and returns `x * x`, for
every Python int `x`. One tactic; no `Val`, no fuel, no AST in sight
(`Examples/python/tut_02/proof.lean`). -/
theorem square_total (x : PyInt) : tut_02.square(x) ==> x * x := by proofs

/-- Whatever `square(x)` returns equals `x * x` — the relational reading,
via the hypothesis-position arrow `⇓` and determinism-modulo-fuel
(`CallsTo.typed_int_eq`, Surface.lean). -/
theorem square_result (x r : PyInt) (h : tut_02.square(x) ⇓ r) : r = x * x := by proofs

/-- Squares are nonnegative — once `square_result` pins the result, the
rest is ordinary mathematics with ordinary Lean tools; the interpreter
never reappears. -/
theorem square_nonneg (x r : PyInt) (h : tut_02.square(x) ⇓ r) : 0 ≤ r := by proofs
