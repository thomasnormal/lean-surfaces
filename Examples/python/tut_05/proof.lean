/-
Proof module for `Examples/python/tut_05/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.python.tut_05.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication.
-/
import LeanModels

namespace Examples.python.tut_05.proof

open LeanModels LeanModels.Python

load_program tut_05 from "Examples/python/tut_05/tut_05.json"

/-- A raise as specified behavior: `py_prove` closes `==>!` goals for
loop-free bodies just like `==>` ones. -/
theorem pymod_zero_raises (a : PyInt) : tut_05.pymod(a, 0) ==>! .zeroDivisionError := by
  py_prove [tut_05]

/-- Total correctness of the countdown for `n ≥ 0` — a single-clause
loop proof. The theorem binder `n` shadows the mutated Python variable
`n`, so `(state := [n])` names the environment slot and the lambda
binder is free to be `k` (tutorial 04's shadowing trap). -/
theorem countdown_total (n : PyInt) (hn : 0 ≤ n) : tut_05.countdown(n) ==> (0 : Int) := by
  py_begin [tut_05]
  py_loop (state := [n])
          (inv := fun (k : Int) => 0 ≤ k)
          (dec := fun (k : Int) => k.toNat)
  all_goals grind

/-- The strengthened partial arrow, free from `countdown_total` by
determinism modulo fuel (`CallsTo.partialTo`, via `py_corollary`). -/
theorem countdown_partial (n : PyInt) (hn : 0 ≤ n) : tut_05.countdown(n) ~~> (0 : Int) := by
  py_corollary [countdown_total]

/-- The refutation of the 42-spec: `~~>` is falsifiable on raising
programs (`PartialTo.not_raises`, Surface.lean). -/
theorem no_partial_spec_for_raising_call : ¬ (tut_05.pymod(7, 0) ~~> (42 : Int)) :=
  fun h => h.not_raises (pymod_zero_raises 7)

end Examples.python.tut_05.proof
