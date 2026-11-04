/-
Examples/python/tut_05 — three-file example layout (see Examples/python/tri/spec.lean
for the pattern rationale): tut_05.py (pure Python), tut_05.json
(generated envelope), THIS FILE (checks + statements, `:= by proofs`),
proof.lean (the real proofs, namespace `Examples.python.tut_05.proof`).
Tutorial 05 (docs/tutorial/05-exceptions-and-partial.md) companion.
-/
import Examples.python.tut_05.proof

open LeanModels LeanModels.Python

load_program tut_05 from "Examples/python/tut_05/tut_05.json"

/-! Tutorial 05 (docs/tutorial/05-exceptions-and-partial.md): the `==>!`
arrow for raising runs, the strengthened partial arrow `~~>`, and why
the weak "if it returns then v" form is banned. -/
#py_check tut_05.pymod(7, 3) = 1
#py_check tut_05.pymod(-7, 3) = 2
#py_check tut_05.pymod(7, -3) = -2
#py_check tut_05.pymod(7, 0) raises .zeroDivisionError
#py_check tut_05.countdown(5) = 0
#py_check tut_05.countdown(0) = 0
#py_check tut_05.countdown(-3) = -3

/-- A raise as specified behavior: for every `a`, `pymod(a, 0)`
terminates by raising `ZeroDivisionError`. `py_prove` closes `==>!`
goals for loop-free bodies just like `==>` ones. -/
theorem pymod_zero_raises (a : PyInt) : tut_05.pymod(a, 0) ==>! .zeroDivisionError := by proofs

/-- Total correctness of the countdown for `n ≥ 0` — a single-clause
loop proof. The theorem binder `n` shadows the mutated Python variable
`n`, so `(state := [n])` names the environment slot and the lambda
binder is free to be `k` (tutorial 04's shadowing trap;
`Examples/python/tut_05/proof.lean`). -/
theorem countdown_total (n : PyInt) (hn : 0 ≤ n) : tut_05.countdown(n) ==> (0 : Int) := by proofs

/-- The strengthened partial arrow: every run of `countdown(n)` with
`n ≥ 0`, at every fuel, either times out or returns exactly `0` — no
exception, no `unsupported`, no other value. Free from `countdown_total`
by determinism modulo fuel (`CallsTo.partialTo`, via `py_corollary`). -/
theorem countdown_partial (n : PyInt) (hn : 0 ≤ n) : tut_05.countdown(n) ~~> (0 : Int) := by proofs

/-- Why the weak reading is banned: `~~>` is *falsifiable* on raising
programs. "If `pymod(7, 0)` returns, it returns 42" is vacuously true —
the call raises. The strengthened `pymod(7, 0) ~~> 42` is refutable, and
here is the refutation (`PartialTo.not_raises`, Surface.lean). -/
theorem no_partial_spec_for_raising_call : ¬ (tut_05.pymod(7, 0) ~~> (42 : Int)) := by proofs
