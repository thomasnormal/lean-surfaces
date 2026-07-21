/-
Examples/fib — three-file example layout (see Examples/tri/spec.lean for
the pattern rationale): fib.py (pure Python), fib.json (generated
envelope), THIS FILE (statements, `:= by proofs`), proof.lean (the real
proofs, namespace `Examples.fib.proof`). The mathematical model `fibSpec`
is defined ONCE, in proof.lean (at root, `def _root_.fibSpec`), so both
files' statements mention the same constant — spec.lean cannot define it
itself without breaking the twin-statement defeq check (`fibSpec` is
recursive, not a literal like the program constants).
-/
import Examples.fib.proof

open LeanModels LeanModels.Python

load_program fib from "Examples/fib/fib.json"

/-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
Surface.lean — fixed generous fuel; minimal-fuel pinning retired) — and
the spec-side model checked at its defining value. -/
#py_check fib(10) = 55
#py_check fib(0) = 0
#py_check fib(1) = 1

#guard fibSpec 10 == 55

set_option warning.simp.varHead false in
/-- **Total correctness**, by strong induction on the mathematical argument
(never on fuel): `fib(k)` terminates and returns `fibSpec k` — stated on
the typed surface (`ToVal Nat` marshals `k`; no `Val`, no fuel). Proof
(base cases by `py_prove`, step case by `py_lift`-threshold IHs and one
symbolic execution): `Examples/fib/proof.lean`. -/
theorem fib_total (k : Nat) : fib(k) ==> fibSpec k := by proofs

set_option warning.simp.varHead false in
/-- `fib(n)` computes the Fibonacci numbers for `n ≥ 0`: any successful
run, at any fuel, yields exactly `.int (fibSpec n.toNat)`. A determinism
corollary of `fib_total` — one `py_corollary` (Surface.lean), instantiated
at `n.toNat` because the total theorem is `Nat`-indexed; the tactic's
built-in `Int.toNat_of_nonneg` bridge (discharged by `hn`) aligns the
marshalled argument. -/
@[spec] theorem fib_spec (n : Int) (hn : 0 ≤ n) {fuel : Nat} {r : Val}
    (h : callFunction fib "fib" #[.int n] fuel = .ok r) :
    r = .int (fibSpec n.toNat) := by proofs

set_option warning.simp.varHead false in
/-- The typed surface form: `fib(n)` relationally yields the mathematical
Fibonacci numbers — no `Val`, no fuel in the statement. -/
@[spec] theorem fib_correct (n r : PyInt) (hn : 0 ≤ n) (h : fib(n) ⇓ r) :
    r = fibSpec n.toNat := by proofs
