import LeanModels.Python.Surface

namespace Examples.python.range_render.proof

open LeanModels LeanModels.Python

load_program range_render from "Examples/python/range_render/range_render.json"

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

#py_check range_render.stop_str(false) = "range(0, False)"
#py_check range_render.stop_str(true) = "range(0, True)"

private theorem zero_decimal : intDecimal 0 = some "0" := by
  unfold intDecimal
  change (if 0 < (10 : Nat) ^ intDigitBudget then
    some (toString (0 : Int)) else none) = _
  rw [if_pos (Nat.pow_pos (show 0 < (10 : Nat) by decide))]
  rfl

theorem stop_str_total (value : PyBool) :
    range_render.stop_str(value) ==>
      "range(0, " ++ (if value then "True" else "False") ++ ")" := by
  cases value <;> refine ⟨32, ?_⟩
  all_goals
    unfold callFunction
    rw [callIn.eq_2]
    py_simp [range_render, reprVal, printOne, zero_decimal]

#print axioms stop_str_total

end Examples.python.range_render.proof
