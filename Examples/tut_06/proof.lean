/-
Proof module for `Examples/tut_06/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.tut_06.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication.
-/
import LeanModels

namespace Examples.tut_06.proof

open LeanModels LeanModels.Python

load_program tut_06 from "Examples/tut_06/tut_06.json"

/-- Failure modes 1 and 2, fixed: `count_up` has a loop, so `py_prove`
cannot close it — `py_begin`/`py_loop` with the *right* invariant can.
The invariant needs both the range conjuncts: dropping `i ≤ n` strands
the exit goal (tutorial 06 shows the stuck state). -/
theorem count_up_total (n : PyInt) (hn : 0 ≤ n) : tut_06.count_up(n) ==> n := by
  py_begin [tut_06]
  py_loop (inv := fun (i : Int) => 0 ≤ i ∧ i ≤ n)
          (dec := fun (i : Int) => (n - i).toNat)
  all_goals grind

end Examples.tut_06.proof
