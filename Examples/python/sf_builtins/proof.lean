/-
Real proofs for Examples/python/sf_builtins/spec.lean — the B1 builtins
(`max`/`min`/`abs`/`int`) acceptance example, on sunfish shapes. The
headline is `lmr_amount`: sunfish.py's deterministic-LMR line
`int(depth >= 4 and i_m >= 8 and val < 0)` proved AS WRITTEN (sf_arith
carries the pre-B1 if/else transliteration of the same line).
-/
import LeanModels

namespace Examples.python.sf_builtins.proof

open LeanModels LeanModels.Python

load_program sf_builtins from "Examples/python/sf_builtins/sf_builtins.json"

/-- Sunfish's deterministic LMR, verbatim: `int()` of the three-way `and`
chain (bool-chain truthiness decided up front, ag_clamp01 pattern). -/
theorem lmr_spec (depth i_m val : PyInt) :
    sf_builtins.lmr_amount(depth, i_m, val) ==>
      (if 4 ≤ depth ∧ 8 ≤ i_m ∧ val < 0 then (1 : Int) else 0) := by
  refine ⟨32, ?_⟩
  by_cases h1 : (4 : Int) ≤ depth <;> by_cases h2 : (8 : Int) ≤ i_m <;>
    by_cases h3 : (val : Int) < 0 <;>
    py_simp [callFunction, sf_builtins, h1, h2, h3] <;> grind

/-- The MTD-bi window clamp: `max(lo, min(hi, x))`, straight-line through
both builtins. -/
theorem clamp_window_spec (x lo hi : PyInt) :
    sf_builtins.clamp_window(x, lo, hi) ==> max lo (min hi x) := by
  py_prove [sf_builtins]

/-- `abs(a - b)` is `|a - b|`. -/
theorem dist_spec (a b : PyInt) :
    sf_builtins.dist(a, b) ==> |a - b| := by
  py_prove [sf_builtins]

end Examples.python.sf_builtins.proof
