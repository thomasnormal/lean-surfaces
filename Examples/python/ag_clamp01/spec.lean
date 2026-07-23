/-
Examples/python/ag_clamp01 — three-file example layout (see Examples/python/tri/spec.lean
for the pattern rationale): ag_clamp01.py (pure Python), ag_clamp01.json
(generated envelope), THIS FILE (statements, `:= by proofs`), proof.lean
(the real proofs, namespace `Examples.python.ag_clamp01.proof`).

Promoted from the doc-validation artifacts (hence the `ag_` stem, kept so
every theorem statement stays byte-identical): it is the tree's only
example of TWO SEQUENTIAL `if`s — the shape outside `py_prove`'s
single-`split` recipe — and the `by_cases`-up-front proof pattern cited by
AGENTS.md's failure table and docs/tutorial/06-when-proofs-fail.md mode 7.
-/
import Examples.python.ag_clamp01.proof

open LeanModels LeanModels.Python

load_program ag_clamp01 from "Examples/python/ag_clamp01/ag_clamp01.json"

/-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
Surface.lean — fixed generous fuel; minimal-fuel pinning retired). -/
#py_check ag_clamp01.clamp01(-5) = 0
#py_check ag_clamp01.clamp01(0) = 0
#py_check ag_clamp01.clamp01(1) = 1
#py_check ag_clamp01.clamp01(7) = 1

/-- Total correctness: `clamp01(x)` terminates and returns `x` clamped to
`[0, 1]`, in min/max form (`max 0 (min 1 x)` agrees with the if-chain on
all three regions). Two *sequential* `if`s are outside `py_prove`'s
single-`split` recipe, so the branches are decided up front with
`by_cases` — the recipe (and why the finisher is `grind`, not `omega`):
`Examples/python/ag_clamp01/proof.lean`. (Not `@[spec]`: the ∃-fuel arrow is not
a Hoare-triple/simp shape — see Examples/python/add/add.py.) -/
theorem clamp01_total (x : PyInt) : ag_clamp01.clamp01(x) ==> max 0 (min 1 x) := by proofs

/-- Strengthened partial correctness: every run, at every fuel, either
times out or returns exactly the clamped value. Free from `clamp01_total`
via determinism modulo fuel (`CallsTo.partialTo`). -/
theorem clamp01_partial (x : PyInt) : ag_clamp01.clamp01(x) ~~> max 0 (min 1 x) := by proofs

set_option warning.simp.varHead false in
/-- `clamp01(x)` returns `max 0 (min 1 x)` on int inputs: any successful
run, at any fuel, yields exactly `.int (max 0 (min 1 x))`. A determinism
corollary of `clamp01_total` — one `py_corollary` (Surface.lean). -/
@[spec] theorem clamp01_run_spec (x : Int) {fuel : Nat} {r : Val}
    (h : callFunction ag_clamp01 "clamp01" #[.int x] fuel = .ok r) :
    r = .int (max 0 (min 1 x)) := by proofs
