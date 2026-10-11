/-
Examples/python/tut_06 — three-file example layout (see Examples/python/tri/spec.lean
for the pattern rationale): tut_06.py (pure Python), tut_06.json
(generated envelope), THIS FILE (checks + statements, `:= by proofs`),
proof.lean (the real proofs, namespace `Examples.python.tut_06.proof`).
Tutorial 06 (docs/tutorial/06-when-proofs-fail.md) companion.
-/
import Examples.python.tut_06.proof

open LeanModels LeanModels.Python

load_program tut_06 from "Examples/python/tut_06/tut_06.json"

/-! Tutorial 06 (docs/tutorial/06-when-proofs-fail.md): the *fixed*
versions of that tutorial's failure walkthroughs. Every broken variant
shown in the tutorial was reproduced against exactly this program. -/
#py_check tut_06.count_up(5) = 5
#py_check tut_06.count_up(0) = 0

/-- Failure modes 1 and 2, fixed: `count_up` has a loop, so `py_prove`
cannot close it — `py_begin`/`py_loop` with the *right* invariant can.
The invariant needs both the range conjuncts: dropping `i ≤ n` strands
the exit goal (tutorial 06 shows the stuck state;
`Examples/python/tut_06/proof.lean`). -/
theorem count_up_total (n : PyInt) (hn : 0 ≤ n) : tut_06.count_up(n) ==> n := by proofs

/-! True division now returns binary64; negative powers remain unfinished
coverage work. The interpreter refuses *loudly* (`Res.unsupported`,
never a wrong value); `unsupported` has no surface arrow on purpose, so
the check stays a raw `#guard … matches`. -/
#py_check tut_06.true_div(7, 2) = Float64.ofBits 0x400c000000000000
#guard (callFunction tut_06 "negative_power" #[.int 2] 100 matches .unsupported _)
