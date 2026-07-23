/-
Proof module for `Examples/python/fib/spec.lean` (three-file example layout).
Every theorem stated in spec.lean is proved here under the same name; the
spec side is `:= by proofs`, which resolves `Examples.python.fib.proof.<decl>`
(Surface.lean). Statements are duplicated between the two files BY DESIGN
(Lean has no forward declarations); the spec-side `:= by proofs` reference
typechecks the duplication. `fibSpec` is deliberately defined at the ROOT
namespace here (not duplicated in spec.lean): the twin statements must
mention the *same* constant — a recursive definition, unlike the program
literals, would not bridge by unfolding.
-/
import LeanModels

namespace Examples.python.fib.proof

open LeanModels LeanModels.Python

load_program fib from "Examples/python/fib/fib.json"

/-- Mathematical Fibonacci: `0, 1, 1, 2, 3, 5, …`. -/
def _root_.fibSpec : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSpec (n + 1) + fibSpec n

set_option warning.simp.varHead false in
/-- **Total correctness**, by strong induction on the mathematical argument
(never on fuel). The base cases are straight-line runs (`py_prove`); in the
step case `py_lift` puts the two IH runs in fuel-threshold form
(`CallsTo.at_least`, i.e. FuelMono), so a single symbolic execution of the
body closes the goal by conditional rewriting. -/
theorem fib_total (k : Nat) : fib(k) ==> fibSpec k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k, ih with
    | 0, _ => py_prove [fib, fibSpec]
    | 1, _ => py_prove [fib, fibSpec]
    | k + 2, ih =>
      -- `py_lift`: the IHs in threshold form, valid at EVERY fuel ≥ f₁/f₂ —
      -- the final conditional rewrite discharges the ≥ side conditions by
      -- omega, so no exact-offset bookkeeping is needed anywhere below.
      py_lift ⟨f₁, h₁⟩ := ih (k + 1) (by omega) with [fib]
      py_lift ⟨f₂, h₂⟩ := ih k (by omega) with [fib]
      refine ⟨f₁ + f₂ + 32, ?_⟩   -- any generous slack works
      rw [callFunction.eq_2]
      py_simp [fib, show ¬((k : Int) + 2 < 2) by omega,
               show (k : Int) + 2 - 1 = ((k + 1 : Nat) : Int) by omega]
      simp (disch := omega) only [h₁, h₂]
      py_simp [fibSpec]

set_option warning.simp.varHead false in
/-- Determinism corollary of `fib_total` — one `py_corollary`
(Surface.lean), instantiated at `n.toNat` (the total theorem is
`Nat`-indexed). -/
theorem fib_spec (n : Int) (hn : 0 ≤ n) {fuel : Nat} {r : Val}
    (h : callFunction fib "fib" #[.int n] fuel = .ok r) :
    r = .int (fibSpec n.toNat) := by
  py_corollary [fib_total n.toNat]

set_option warning.simp.varHead false in
/-- The typed surface form, another `py_corollary` of `fib_total`. -/
theorem fib_correct (n r : PyInt) (hn : 0 ≤ n) (h : fib(n) ⇓ r) :
    r = fibSpec n.toNat := by
  py_corollary [fib_total n.toNat]

end Examples.python.fib.proof
