/-
Examples/add — three-file example layout (see Examples/tri/spec.lean for
the pattern rationale): add.py (pure Python), add.json (generated
envelope), THIS FILE (statements, `:= by proofs`), proof.lean (the real
proofs, namespace `Examples.add.proof`).
-/
import Examples.add.proof

open LeanModels LeanModels.Python

load_program add from "Examples/add/add.json"

/-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
Surface.lean — fixed generous fuel; minimal-fuel pinning retired). -/
#py_check add(2, 3) = 5
#py_check add(-2, 3) = 1

/-- The typed surface form: total correctness — `add` terminates and
returns `a + b` — with no `Val`, no fuel, one tactic
(`Examples/add/proof.lean`). (Not `@[spec]`: that attribute takes
Hoare-triple/simp shapes; the ∃-fuel arrow is neither.) -/
theorem add_total (a b : PyInt) : add(a, b) ==> a + b := by proofs

set_option warning.simp.varHead false in
/-- `add(a, b)` returns `a + b` on int inputs: any successful run, at any
fuel, yields exactly `.int (a + b)` (partial correctness). A determinism
corollary of `add_total` — one `py_corollary` (Surface.lean). -/
@[spec] theorem add_spec (a b : Int) {fuel : Nat} {r : Val}
    (h : callFunction add "add" #[.int a, .int b] fuel = .ok r) :
    r = .int (a + b) := by proofs

/-- The strengthened partial arrow: every run of `add(a, b)`, at every
fuel, either times out or returns exactly `a + b` — no exception, no
`unsupported`, no other value. Note `add_spec` alone could NOT give this
(it speaks only about `.ok` results); it is instead free from `add_total`,
because the interpreter is deterministic modulo fuel and total correctness
subsumes the strengthened partial judgment (`CallsTo.partialTo`). -/
theorem add_partial (a b : PyInt) : add(a, b) ~~> a + b := by proofs

/-! Delaborator regression (LeanModels/Python/Delab.lean): the statements
print back in surface notation — the goal state is the interface. -/

/-- info: add_total (a b : PyInt) : add(a, b) ==> a + b -/
#guard_msgs in
#check add_total

/-- info: add_partial (a b : PyInt) : add(a, b) ~~> a + b -/
#guard_msgs in
#check add_partial
