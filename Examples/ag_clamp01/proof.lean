/-
Proof module for `Examples/ag_clamp01/spec.lean` (three-file example
layout). Every theorem stated in spec.lean is proved here under the same
name; the spec side is `:= by proofs`, which resolves
`Examples.ag_clamp01.proof.<decl>` (Surface.lean). Statements are
duplicated between the two files BY DESIGN (Lean has no forward
declarations); the spec-side `:= by proofs` reference typechecks the
duplication.
-/
import LeanModels

namespace Examples.ag_clamp01.proof

open LeanModels LeanModels.Python

load_program ag_clamp01 from "Examples/ag_clamp01/ag_clamp01.json"

/-- Total correctness in the two-sequential-`if`s shape: outside
`py_prove`'s single-`split` recipe — its mop-up rewrites the second
surviving `ite` into a disjunction `split` can no longer attack — so the
branches are decided up front with `by_cases` and the case facts are
passed to `py_simp` as rewrites. The finisher is `grind`, not `omega`:
with the binder at `PyInt`, the `by_cases` comparisons elaborate
brand-headed (`@LT.lt PyInt …`), and `omega` skips any comparison whose
head type is the brand; `grind` matches up to reducible unfolding and
closes all four cases (docs/tutorial/06-when-proofs-fail.md, modes 5
and 7). -/
theorem clamp01_total (x : PyInt) : ag_clamp01.clamp01(x) ==> max 0 (min 1 x) := by
  refine ⟨32, ?_⟩
  by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;>
    py_simp [callFunction, ag_clamp01, h1, h2] <;> grind

/-- Strengthened partial correctness, free from `clamp01_total` via
`CallsTo.partialTo` (determinism modulo fuel). -/
theorem clamp01_partial (x : PyInt) : ag_clamp01.clamp01(x) ~~> max 0 (min 1 x) := by
  py_corollary [clamp01_total]

/-- Determinism corollary of `clamp01_total` — one `py_corollary`
(Surface.lean). -/
theorem clamp01_run_spec (x : Int) {fuel : Nat} {r : Val}
    (h : callFunction ag_clamp01 "clamp01" #[.int x] fuel = .ok r) :
    r = .int (max 0 (min 1 x)) := by
  py_corollary [clamp01_total]

end Examples.ag_clamp01.proof
