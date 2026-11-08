/-
Proof module for `Examples/python/my_abs/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.python.my_abs.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication.
-/
import LeanModels

namespace Examples.python.my_abs.proof

open LeanModels LeanModels.Python

load_program my_abs from "Examples/python/my_abs/my_abs.json"

/-- Total correctness: `py_prove`'s branch-splitting alternative `split`s
the residual `ite` from the symbolic `if x < 0:` and finishes each side
with `omega` (which understands `natAbs` natively). -/
theorem my_abs_spec (x : PyInt) : my_abs(x) ==> |x| := by
  refine ⟨32, ?_⟩
  by_cases h : x < 0
  · let xi : Int := x
    have hxi : xi < 0 := by simpa [xi] using h
    have hneg : 0 ≤ -xi := by omega
    have habsxi : (Int.natAbs xi : Int) = -xi := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg hneg
    have habs : (Int.natAbs x : Int) = -x := by simpa [xi] using habsxi
    py_simp [callFunction, callIn, my_abs, h, habs, pythonTopCallDepth,
      pythonRecursionLimit, Run.finishCallAt, Run.leaveCallDepth,
      Run.toPublic, Run.toPublic_ok, RVal.freezeB]
  · let xi : Int := x
    have hxi : 0 ≤ xi := by
      have : ¬ xi < 0 := by simpa [xi] using h
      omega
    have habsxi : (Int.natAbs xi : Int) = xi := Int.natAbs_of_nonneg hxi
    have habs : (Int.natAbs x : Int) = x := by simpa [xi] using habsxi
    py_simp [callFunction, callIn, my_abs, h, habs, pythonTopCallDepth,
      pythonRecursionLimit, Run.finishCallAt, Run.leaveCallDepth,
      Run.toPublic, Run.toPublic_ok, RVal.freezeB]

/-- Determinism corollary of `my_abs_spec` — one `py_corollary`
(Surface.lean). -/
theorem my_abs_run_spec (x : Int) {fuel : Nat} {r : Val}
    (h : callFunction my_abs "my_abs" #[.int x] fuel = .ok r) :
    r = .int |x| := by
  py_corollary [my_abs_spec]

end Examples.python.my_abs.proof
