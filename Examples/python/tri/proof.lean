/-
Proof module for `Examples/python/tri/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.python.tri.proof.<decl>`
(Surface.lean). The statements are duplicated between the two files BY
DESIGN — Lean has no forward declarations — and the duplication is
typechecked by that spec-side reference: a drifted statement fails to
close. This file loads its own copy of the program literal (same envelope,
different constant); `proofs` bridges the two constants by unfolding.
-/
import LeanModels

namespace Examples.python.tri.proof

open LeanModels LeanModels.Python

load_program tri from "Examples/python/tri/tri.json"

/-- Total correctness for `n ≥ 0`, by the VC walker (`py_vcgen`,
VCTactic.lean): one call bridges the arrow goal to the whole-body triple
and walks it, opening the loop from the same two clauses `py_loop` took —
the invariant (`total = 0 + 1 + ⋯ + (i-1)`, stated multiplication-free
as `2*total = i*(i-1)`, plus the range `0 ≤ i ≤ n + 1`) and the measure
`n + 1 - i`. Residual goals are pure arithmetic on named atoms: the
`return` (exit algebra: the negated test and the range force
`i' = n + 1`, then `grind` finishes the division), then preservation,
decrease, and the initial invariant, all closed by `grind`. No `Val`, no
fuel, no AST anywhere. -/
theorem tri_total (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
  py_vcgen [tri]
    (inv := fun (total i : Int) => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1))
    (dec := fun (total i : Int) => (n + 1 - i).toNat)
  case ret =>
    obtain rfl : i' = n + 1 := by omega
    grind
  all_goals grind

/-- Total correctness for `n < 0`: the loop never runs, all at constant
fuel. -/
theorem tri_neg_total (n : PyInt) (hn : n < 0) : tri(n) ==> (0 : Int) := by
  have h0 : ¬ ((0 : Int) ≤ n) := by have hn' : (0 : Int) > n := hn; omega
  exact CallsTo.intro 8 (by py_simp [callFunction, callIn, execWhile, tri, h0])

/-- Determinism corollary of `tri_total` — one `py_corollary`
(Surface.lean). -/
theorem tri_spec (n : Int) (hn : 0 ≤ n) {fuel : Nat} {r : Val}
    (h : callFunction tri "tri" #[.int n] fuel = .ok r) :
    r = .int (n * (n + 1) / 2) := by
  py_corollary [tri_total]

/-- Determinism corollary of `tri_neg_total`. -/
theorem tri_neg_spec (n : Int) (hn : n < 0) {fuel : Nat} {r : Val}
    (h : callFunction tri "tri" #[.int n] fuel = .ok r) :
    r = .int 0 := by
  py_corollary [tri_neg_total]

/-- The typed surface form, another `py_corollary` of `tri_total`. -/
theorem tri_correct (n r : PyInt) (hn : 0 ≤ n) (h : tri(n) ⇓ r) :
    r = n * (n + 1) / 2 := by
  py_corollary [tri_total]

end Examples.python.tri.proof
