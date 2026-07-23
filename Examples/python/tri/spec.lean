/-
Examples/python/tri — the three-file example layout (the migration pattern):

  tri.py     — pure Python, no `# lean[` blocks
  tri.json   — generated envelope (extractors/python/extract.py; the
               extractor emits no companion for a block-less source)
  spec.lean  — THIS FILE: program load, non-vacuity checks, and every
               theorem STATEMENT, each proved `:= by proofs`
  proof.lean — the real proofs (namespace `Examples.python.tri.proof`)

`proofs` (Surface.lean) resolves each declaration's name against the
sibling proof module. The statement duplication between spec and proof is
BY DESIGN (Lean has no forward declarations) and is typechecked by the
`:= by proofs` reference.
-/
import Examples.python.tri.proof

open LeanModels LeanModels.Python

load_program tri from "Examples/python/tri/tri.json"

/-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
Surface.lean — fixed generous fuel; minimal-fuel pinning retired). -/
#py_check tri(10) = 55
#py_check tri(0) = 0
#py_check tri(-3) = 0

/-- Total correctness for `n ≥ 0`: `tri(n)` terminates and returns the
`n`-th triangular number `n * (n + 1) / 2`. Proof (invariant/measure
clause form, `py_begin`/`py_loop`): `Examples/python/tri/proof.lean`. -/
theorem tri_total (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by proofs

/-- Total correctness for `n < 0`: the loop never runs and `tri(n)` returns
`0`. -/
theorem tri_neg_total (n : PyInt) (hn : n < 0) : tri(n) ==> (0 : Int) := by proofs

set_option warning.simp.varHead false in
/-- `tri(n)` returns the `n`-th triangular number `n*(n+1)/2` for `n ≥ 0`:
any successful run, at any fuel, yields exactly `.int (n*(n+1)/2)`. A
determinism corollary of `tri_total`. -/
@[spec] theorem tri_spec (n : Int) (hn : 0 ≤ n) {fuel : Nat} {r : Val}
    (h : callFunction tri "tri" #[.int n] fuel = .ok r) :
    r = .int (n * (n + 1) / 2) := by proofs

set_option warning.simp.varHead false in
/-- `tri(n)` returns `0` for `n < 0` (the loop body never runs). A
determinism corollary of `tri_neg_total`. -/
@[spec] theorem tri_neg_spec (n : Int) (hn : n < 0) {fuel : Nat} {r : Val}
    (h : callFunction tri "tri" #[.int n] fuel = .ok r) :
    r = .int 0 := by proofs

set_option warning.simp.varHead false in
/-- The typed surface form of `tri_spec`: binders are `PyInt`, the result is
bound relationally with `⇓`, and neither `Val` nor fuel appears. -/
@[spec] theorem tri_correct (n r : PyInt) (hn : 0 ≤ n) (h : tri(n) ⇓ r) :
    r = n * (n + 1) / 2 := by proofs
