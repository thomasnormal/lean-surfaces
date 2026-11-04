/-
Examples/python/gcd — three-file example layout (see Examples/python/tri/spec.lean for
the pattern rationale): gcd.py (pure Python), gcd.json (generated
envelope), THIS FILE (statements, `:= by proofs`), proof.lean (the real
proofs, namespace `Examples.python.gcd.proof`).
-/
import Examples.python.gcd.proof

open LeanModels LeanModels.Python

load_program gcd from "Examples/python/gcd/gcd.json"

/-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
Surface.lean — fixed generous fuel; minimal-fuel pinning retired). -/
#py_check gcd(12, 18) = 6
#py_check gcd(18, 12) = 6
#py_check gcd(5, 0) = 5
#py_check gcd(0, 5) = 5
#py_check gcd(7, 13) = 1

/-! CPython-divergence documentation (why the sign hypotheses below are
NOT optional): Python's `%` is `Int.fmod`, so a negative operand keeps the
loop below zero and `gcd(4, -6)` terminates at `-2` — matching CPython
(differentially tested, harness/cases.json) — while `Int.gcd 4 (-6) = 2`.
The unguarded spec `gcd(a, b) ==> Int.gcd a b` is *false*
(docs/spec-surface.md §3). (The second line is a spec-side math fact, not
a call — raw `#guard`.) -/
#py_check gcd(4, -6) = -2
#guard Int.gcd 4 (-6) == 2

/-- **Total correctness** (gallery example 3): for nonnegative inputs
`gcd(a, b)` terminates and returns `Int.gcd a b` (Nat-valued, marshalled
via `ToVal Nat`). Proof (invariant/measure clause form,
`py_begin`/`py_loop` with the `(state := [a, b])` shadowing escape hatch):
`Examples/python/gcd/proof.lean`. (Not `@[spec]`: the ∃-fuel arrow is not a
Hoare-triple/simp shape — see `Examples/python/add/add.py`.) -/
theorem gcd_total (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : gcd(a, b) ==> Int.gcd a b := by proofs

/-- **Strengthened partial correctness** (the `~~>` arrow, `PartialTo`):
every run of `gcd(a, b)` at every fuel either times out or returns exactly
`Int.gcd a b` — no exception, no `unsupported`, no other value. The naive
"if it returns `.ok` then `v`" reading would be vacuously provable here
even on the (false) unguarded statement; `~~>` is the falsifiable form. -/
theorem gcd_partial (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : gcd(a, b) ~~> Int.gcd a b := by proofs

set_option warning.simp.varHead false in
/-- `gcd(a, b)` returns `Int.gcd a b` on nonneg int inputs: any successful
run, at any fuel, yields exactly `.int (Int.gcd a b)`. A determinism
corollary of `gcd_total`. -/
@[spec] theorem gcd_spec (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) {fuel : Nat} {r : Val}
    (h : callFunction gcd "gcd" #[.int a, .int b] fuel = .ok r) :
    r = .int (Int.gcd a b) := by proofs
