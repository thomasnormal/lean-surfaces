/-
Examples/python/sf_builtins — three-file example layout. The B1 builtins
(`max`/`min`/`abs`/`int`) acceptance example, on sunfish shapes. The
headline is `lmr_amount`: sunfish.py's deterministic-LMR line
`int(depth >= 4 and i_m >= 8 and val < 0)` proved AS WRITTEN — sf_arith
carries the pre-B1 if/else transliteration of the same line (benchmark
fix F-5, now closed).
-/
import Examples.python.sf_builtins.proof

open LeanModels LeanModels.Python

load_program sf_builtins from "Examples/python/sf_builtins/sf_builtins.json"

/-! Non-vacuity: concrete runs (values cross-checked against CPython). -/
#py_check sf_builtins.lmr_amount(4, 8, -1) = 1
#py_check sf_builtins.lmr_amount(3, 8, -1) = 0
#py_check sf_builtins.lmr_amount(4, 7, -1) = 0
#py_check sf_builtins.lmr_amount(4, 8, 0) = 0
#py_check sf_builtins.clamp_window(5, 0, 10) = 5
#py_check sf_builtins.clamp_window(-3, 0, 10) = 0
#py_check sf_builtins.clamp_window(15, 0, 10) = 10
#py_check sf_builtins.dist(3, 7) = 4
#py_check sf_builtins.dist(7, 3) = 4

/-- Sunfish's deterministic LMR, verbatim `int(...)` of the `and` chain. -/
theorem lmr_spec (depth i_m val : PyInt) :
    sf_builtins.lmr_amount(depth, i_m, val) ==>
      (if 4 ≤ depth ∧ 8 ≤ i_m ∧ val < 0 then (1 : Int) else 0) := by proofs

/-- The MTD-bi window clamp: `max(lo, min(hi, x))`. -/
theorem clamp_window_spec (x lo hi : PyInt) :
    sf_builtins.clamp_window(x, lo, hi) ==> max lo (min hi x) := by proofs

/-- `abs(a - b)` is `|a - b|`. -/
theorem dist_spec (a b : PyInt) :
    sf_builtins.dist(a, b) ==> |a - b| := by proofs
