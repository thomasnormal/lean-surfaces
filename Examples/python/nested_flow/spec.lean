/-
Examples/python/nested_flow — three-file example layout (see
Examples/python/tri/spec.lean for the pattern rationale): nested_flow.py
(pure Python), nested_flow.json (generated envelope), THIS FILE
(statements, `:= by proofs`), proof.lean (the real proofs, namespace
`Examples.python.nested_flow.proof`).

THE CONTROL-FLOW STRESS EXAMPLE: `first_factor` is trial division whose
divisibility test is itself a loop — a while nested in a while, a `break`
inside an `if` in the inner body, and a `return` out of the middle of the
outer loop. One loop with one exit is all `py_begin`/`py_loop` can open,
so this example is proved by the VC walker `py_vcgen` (VCTactic.lean)
from two `inv`/`dec` clause pairs plus one `exit2` fact. The spec is a
NAMED model function: mathlib's `Nat.minFac`, the least prime factor.
-/
import Examples.python.nested_flow.proof

open LeanModels LeanModels.Python

load_program nested_flow from "Examples/python/nested_flow/nested_flow.json"

/-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
Surface.lean — fixed generous fuel). Composite, prime-power, semiprime,
and prime inputs. -/
#py_check nested_flow.first_factor(2) = 2
#py_check nested_flow.first_factor(9) = 3
#py_check nested_flow.first_factor(15) = 3
#py_check nested_flow.first_factor(49) = 7
#py_check nested_flow.first_factor(91) = 7
#py_check nested_flow.first_factor(97) = 97

/-- **Total correctness**: for `2 ≤ n`, `first_factor(n)` terminates and
returns the least prime factor of `n` (mathlib's `Nat.minFac`; `n` itself
when `n` is prime). Proof (nested loops + break + mid-loop return,
`py_vcgen` from two clause pairs and one exit fact):
`Examples/python/nested_flow/proof.lean`. -/
theorem first_factor_total (n : PyInt) (hn : 2 ≤ n) :
    nested_flow.first_factor(n) ==> (n.toNat.minFac : PyInt) := by proofs

/-- Typed relational corollary (determinism modulo fuel): ANY `⇓`-bound
result of `first_factor(n)` on `2 ≤ n` is the least prime factor. -/
theorem first_factor_correct (n r : PyInt) (hn : 2 ≤ n)
    (h : nested_flow.first_factor(n) ⇓ r) : r = (n.toNat.minFac : PyInt) := by proofs
