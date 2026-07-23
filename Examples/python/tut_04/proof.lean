/-
Proof module for `Examples/python/tut_04/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.python.tut_04.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication. `factSpec` and its bridge lemma
`factSpec_step` are deliberately defined at the ROOT namespace here (the
fib pattern — see Examples/python/fib/proof.lean): the twin statements must
mention the *same* constant, and a recursive definition, unlike the
program literals, would not bridge by unfolding.
-/
import LeanModels

namespace Examples.python.tut_04.proof

open LeanModels LeanModels.Python

load_program tut_04 from "Examples/python/tut_04/tut_04.json"

/-- Mathematical factorial: `1, 1, 2, 6, 24, 120, …` — the spec-side
model, `Int`-valued so it lands where the marshalled result lives. -/
def _root_.factSpec : Nat → Int
  | 0 => 1
  | n + 1 => (n + 1 : Int) * factSpec n

/-- The unfolding step of `factSpec` in the exact `Int` shape the loop
invariant produces: for `1 ≤ i`, `factSpec i.toNat` peels off one factor
`i`. `grind` consumes this in the invariant-preservation goal. -/
theorem _root_.factSpec_step (i : Int) (hi : 1 ≤ i) :
    factSpec i.toNat = i * factSpec (i - 1).toNat := by
  have h : i.toNat = (i - 1).toNat + 1 := by omega
  rw [h, factSpec]
  congr 1
  omega

/-- Total correctness for `n ≥ 0`: `fact(n)` terminates and returns `n!`
— in clause form (LoopTactic.lean). Invariant: `r` holds the factorial
of everything already multiplied in (`r = factSpec (i-1).toNat`), plus
the range `1 ≤ i ≤ n + 1`; measure: iterations left, `(n + 1 - i)`.
Residual goals: the exit algebra (`hcont` + range force `i' = n + 1`,
then `hinv3` *is* the claim), and preservation/decrease/initial all fall
to `grind` armed with `factSpec`'s equations and `factSpec_step`. -/
theorem fact_total (n : PyInt) (hn : 0 ≤ n) : tut_04.fact(n) ==> factSpec n.toNat := by
  py_begin [tut_04]
  py_loop (inv := fun (r i : Int) => 1 ≤ i ∧ i ≤ n + 1 ∧ r = factSpec (i - 1).toNat)
          (dec := fun (r i : Int) => (n + 1 - i).toNat)
  · obtain rfl : i' = n + 1 := by omega
    simpa using hinv3
  all_goals grind [factSpec, factSpec_step]

set_option warning.simp.varHead false in
/-- Determinism corollary of `fact_total` — one `py_corollary`
(Surface.lean). -/
theorem fact_spec (n : Int) (hn : 0 ≤ n) {fuel : Nat} {r : Val}
    (h : callFunction tut_04 "fact" #[.int n] fuel = .ok r) :
    r = .int (factSpec n.toNat) := by
  py_corollary [fact_total]

set_option warning.simp.varHead false in
/-- The typed surface form, another `py_corollary` of `fact_total`. -/
theorem fact_correct (n r : PyInt) (hn : 0 ≤ n) (h : tut_04.fact(n) ⇓ r) :
    r = factSpec n.toNat := by
  py_corollary [fact_total]

end Examples.python.tut_04.proof
