/-
Examples/arith — three-file example layout (see Examples/tri/spec.lean
for the pattern rationale): arith.py (pure Python), arith.json (generated
envelope), THIS FILE (the non-vacuity check matrix + statements,
`:= by proofs`), proof.lean (the real proofs, namespace
`Examples.arith.proof`). This example is primarily a semantic check
matrix; its two theorems specify the runtime-error paths.
-/
import Examples.arith.proof

open LeanModels LeanModels.Python

load_program arith from "Examples/arith/arith.json"

/-! Non-vacuity: concrete runs of every function in surface syntax
(`#py_check`, Surface.lean), including the error and short-circuit paths.
The `unsupported` outcome has no surface form (it is a semantic-tier gap,
not a Python result) — that one check stays a raw `#guard … matches`. The
full differential matrix against CPython lives in harness/cases.json. -/
#py_check arith.floordiv(7, 2) = 3
#py_check arith.floordiv(-7, 2) = -4
#py_check arith.floordiv(7, 0) raises .zeroDivisionError
#py_check arith.mod(-7, 2) = 1
#py_check arith.mod(7, -2) = -1
#py_check arith.mod(7, 0) raises .zeroDivisionError
#py_check arith.powi(2, 0) = 1
#py_check arith.powi(-2, 3) = -8
#guard (callFunction arith "powi" #[.int 2, .int (-1)] 20 matches .unsupported _)
#py_check arith.choose(0, 5) = 5
#py_check arith.choose(3, 7) = 3
#py_check arith.chain(1, 2, 3) = true
#py_check arith.chain(1, 3, 2) = false
#py_check arith.idx(0) = 10
#py_check arith.idx(-1) = 30
#py_check arith.idx(3) raises .indexError

/-- Exceptions as specified behavior (docs/spec-surface.md example 4, in
its v0 form: the tier has no `raise` statement, but *runtime* errors are
real and provable): `floordiv(a, 0)` terminates by raising
`ZeroDivisionError`, for every `a` — the `==>!` arrow (`Raises`,
Surface.lean). The error path is loop-free, so `py_prove` closes it
(`Examples/arith/proof.lean`). -/
theorem floordiv_zero (a : PyInt) : arith.floordiv(a, 0) ==>! .zeroDivisionError := by proofs

/-- Same shape for `%`: `mod(a, 0)` raises for every `a`. -/
theorem mod_zero (a : PyInt) : arith.mod(a, 0) ==>! .zeroDivisionError := by proofs
