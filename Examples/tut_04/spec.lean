/-
Examples/tut_04 — three-file example layout (see Examples/tri/spec.lean
for the pattern rationale): tut_04.py (pure Python), tut_04.json
(generated envelope), THIS FILE (checks + statements, `:= by proofs`),
proof.lean (the real proofs, namespace `Examples.tut_04.proof`).
Tutorial 04 (docs/tutorial/04-loops.md) companion. The mathematical model
`factSpec` and its bridge lemma `factSpec_step` are defined ONCE, in
proof.lean at the root namespace (the fib pattern: the twin statements
must mention the *same* constant — a recursive definition, unlike the
program literals, would not bridge by unfolding).
-/
import Examples.tut_04.proof

open LeanModels LeanModels.Python

load_program tut_04 from "Examples/tut_04/tut_04.json"

/-! Tutorial 04 (docs/tutorial/04-loops.md): the worked exercise —
factorial by loop, proved end-to-end with `py_begin`/`py_loop` — and the
spec-side model checked at its defining value. -/
#py_check tut_04.fact(5) = 120
#py_check tut_04.fact(1) = 1
#py_check tut_04.fact(0) = 1
#py_check tut_04.fact(-2) = 1

#guard factSpec 5 == 120

/-- Total correctness for `n ≥ 0`: `fact(n)` terminates and returns `n!`
— in clause form (LoopTactic.lean). Invariant: `r` holds the factorial
of everything already multiplied in (`r = factSpec (i-1).toNat`), plus
the range `1 ≤ i ≤ n + 1`; measure: iterations left, `(n + 1 - i)`.
Proof: `Examples/tut_04/proof.lean`. -/
theorem fact_total (n : PyInt) (hn : 0 ≤ n) : tut_04.fact(n) ==> factSpec n.toNat := by proofs

set_option warning.simp.varHead false in
/-- `fact(n)` returns `n!` for `n ≥ 0`: any successful run, at any fuel,
yields exactly `.int (factSpec n.toNat)`. A determinism corollary of
`fact_total` — one `py_corollary` (Surface.lean). -/
@[spec] theorem fact_spec (n : Int) (hn : 0 ≤ n) {fuel : Nat} {r : Val}
    (h : callFunction tut_04 "fact" #[.int n] fuel = .ok r) :
    r = .int (factSpec n.toNat) := by proofs

set_option warning.simp.varHead false in
/-- The typed surface form: binders are `PyInt`, the result is bound
relationally with `⇓`, and neither `Val` nor fuel appears. -/
@[spec] theorem fact_correct (n r : PyInt) (hn : 0 ≤ n) (h : tut_04.fact(n) ⇓ r) :
    r = factSpec n.toNat := by proofs
