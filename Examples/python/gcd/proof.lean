/-
Proof module for `Examples/python/gcd/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.python.gcd.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side reference typechecks it.
-/
import LeanModels

namespace Examples.python.gcd.proof

open LeanModels LeanModels.Python

load_program gcd from "Examples/python/gcd/gcd.json"

/-- Core of `gcd_total` (`py_vcgen`, VCTactic.lean). Clause binders must
be the Python names `a`/`b`, and the invariant must mention the *initial*
values — so those get capitalized binders `A`/`B` (the walker's
counterpart of `py_loop`'s `(state := …)` escape hatch). Residuals: exit
fact, one Euclid step (`gcd_fmod_step` + `Int.fmod_nonneg`, Surface.lean),
measure decrease, and the `return` (`grind` bridges `natAbs`). -/
private theorem gcd_core (A B : PyInt) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    gcd(A, B) ==> Int.gcd A B := by
  py_vcgen [gcd]
    (inv := fun (a b : Int) => 0 ≤ a ∧ 0 ≤ b ∧ Int.gcd a b = Int.gcd A B)
    (dec := fun (a b : Int) => b.toNat)
  · exact ⟨a, ⟨rfl, hx⟩, hcore.1, by rw [← hcore.2.2, hx, Int.gcd_zero_right]⟩
  · exact Int.fmod_nonneg hinv1 hinv2
  · rw [gcd_fmod_step hinv1 hinv2]; exact hinv3
  · have := Int.fmod_lt_of_pos a (show (0:Int) < b by omega)
    have := Int.fmod_nonneg hinv1 hinv2
    omega
  · grind [Int.gcd_zero_right, Int.natAbs_of_nonneg]

/-- Total correctness: the core above at the public binders. -/
theorem gcd_total (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : gcd(a, b) ==> Int.gcd a b :=
  gcd_core a b ha hb

/-- The `~~>` form is free from `gcd_total` via `CallsTo.partialTo`
(determinism modulo fuel): one induction serves both arrows. -/
theorem gcd_partial (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : gcd(a, b) ~~> Int.gcd a b := by
  py_corollary [gcd_total]

/-- Determinism corollary of `gcd_total` — one `py_corollary`
(Surface.lean). -/
theorem gcd_spec (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) {fuel : Nat} {r : Val}
    (h : callFunction gcd "gcd" #[.int a, .int b] fuel = .ok r) :
    r = .int (Int.gcd a b) := by
  py_corollary [gcd_total]

end Examples.python.gcd.proof
