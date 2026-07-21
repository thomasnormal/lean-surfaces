/-
Examples/tut_06 — three-file example layout (see Examples/tri/spec.lean
for the pattern rationale): tut_06.py (pure Python), tut_06.json
(generated envelope), THIS FILE (checks + statements, `:= by proofs`),
proof.lean (the real proofs, namespace `Examples.tut_06.proof`).
Tutorial 06 (docs/tutorial/06-when-proofs-fail.md) companion.
-/
import Examples.tut_06.proof

open LeanModels LeanModels.Python

load_program tut_06 from "Examples/tut_06/tut_06.json"

/-! Tutorial 06 (docs/tutorial/06-when-proofs-fail.md): the *fixed*
versions of that tutorial's failure walkthroughs. Every broken variant
shown in the tutorial was reproduced against exactly this program. -/
#py_check tut_06.count_up(5) = 5
#py_check tut_06.count_up(0) = 0

/-- Failure modes 1 and 2, fixed: `count_up` has a loop, so `py_prove`
cannot close it — `py_begin`/`py_loop` with the *right* invariant can.
The invariant needs both the range conjuncts: dropping `i ≤ n` strands
the exit goal (tutorial 06 shows the stuck state;
`Examples/tut_06/proof.lean`). -/
theorem count_up_total (n : PyInt) (hn : 0 ≤ n) : tut_06.count_up(n) ==> n := by proofs

/-! Failure mode 6: `a / b` is true division — a float, outside the v0
semantic tier. The interpreter refuses *loudly* (`Res.unsupported`,
never a wrong value); `unsupported` has no surface arrow on purpose, so
the check stays a raw `#guard … matches`. -/
#guard (callFunction tut_06 "true_div" #[.int 7, .int 2] 100 matches .unsupported _)
