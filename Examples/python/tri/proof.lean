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

/-- Total correctness for `n ≥ 0`, in clause form (LoopTactic.lean):
`py_begin` symbolically executes the entry up to the loop; `py_loop` proves
the loop by the generic while rule from just two clauses — the invariant
(`total = 0 + 1 + ⋯ + (i-1)`, stated multiplication-free as
`2*total = i*(i-1)`, plus the range `0 ≤ i ≤ n + 1`) and the decreasing
measure `n + 1 - i` — deriving the logical state, its environment
rendering, the test value, and the body's step by unification. Residual
goals are pure arithmetic on named atoms: the exit algebra (first bullet:
`¬ i' ≤ n` and the range force `i' = n + 1`, then `grind` finishes the
division), then invariant preservation, measure decrease, and the initial
invariant, all closed by `grind`. No `Val`, no fuel, no AST anywhere. -/
theorem tri_total (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
  py_begin [tri]
  py_loop (inv := fun (total i : Int) => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1))
          (dec := fun (total i : Int) => (n + 1 - i).toNat)
  · obtain rfl : i' = n + 1 := by omega
    grind
  all_goals grind

/-- Total correctness for `n < 0`: the loop never runs, all at constant
fuel. -/
theorem tri_neg_total (n : PyInt) (hn : n < 0) : tri(n) ==> (0 : Int) := by
  have h0 : ¬ ((0 : Int) ≤ n) := by have hn' : (0 : Int) > n := hn; omega
  exact CallsTo.intro 8 (by py_simp [callFunction, execWhile, tri, h0])

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
