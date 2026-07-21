/-
Proof module for `Examples/gcd/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.gcd.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication.
-/
import LeanModels

namespace Examples.gcd.proof

open LeanModels LeanModels.Python

load_program gcd from "Examples/gcd/gcd.json"

/-- Total correctness in clause form (LoopTactic.lean). The invariant is
"both nonneg ∧ `Int.gcd` unchanged from the initial values", the measure
is the divisor itself; `(state := [a, b])` names the loop's environment
variables because the theorem binders `a b` shadow the Python names and
the invariant must mention the *initial* values (this is exactly the
escape hatch's purpose). Residual goals on named atoms (`x`/`y`, exit
state `x'`/`y'`, invariant conjuncts `hinv1`–`hinv3`): exit algebra
(`y' = 0` collapses the gcd, `grind` bridges `natAbs`), one Euclid step
(`gcd_fmod_step` + `Int.fmod_nonneg`, Surface.lean), measure decrease
(`0 ≤ x.fmod y < y`), and the initial invariant. -/
theorem gcd_total (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : gcd(a, b) ==> Int.gcd a b := by
  py_begin [gcd]
  py_loop (state := [a, b])
          (inv := fun (x y : Int) => 0 ≤ x ∧ 0 ≤ y ∧ Int.gcd x y = Int.gcd a b)
          (dec := fun (x y : Int) => y.toNat)
  · grind [Int.gcd_zero_right, Int.natAbs_of_nonneg]
  · exact ⟨hinv2, Int.fmod_nonneg hinv1 hinv2, by rw [gcd_fmod_step hinv1 hinv2, hinv3]⟩
  · have := Int.fmod_lt_of_pos x (show (0:Int) < y by omega)
    have := Int.fmod_nonneg hinv1 hinv2
    omega
  · exact ⟨ha, hb, trivial⟩

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

end Examples.gcd.proof
