import Examples.python.range_render.proof

open LeanModels LeanModels.Python

load_program range_render from "Examples/python/range_render/range_render.json"

set_option maxRecDepth 8192

#py_check range_render.stop_str(false) = "range(0, False)"
#py_check range_render.stop_str(true) = "range(0, True)"
#py_check range_render.stop_str(0) = "range(0, 0)"
#py_check range_render.stop_str(1) = "range(0, 1)"
#py_check range_render.bounds_str(false, true) = "range(False, True)"
#py_check range_render.bounds_str(true, false) = "range(True, False)"
#py_check range_render.bounds_str(true, 5) = "range(True, 5)"
#py_check range_render.step_str(false, true, true) = "range(False, True)"
#py_check range_render.step_str(true, false, -1) = "range(True, False, -1)"
#py_check range_render.step_str(true, 5, 2) = "range(True, 5, 2)"
#py_check range_render.stop_fstring(false) = "range(0, False)"
#py_check range_render.bounds_fstring(false, true) = "range(False, True)"
#py_check range_render.step_fstring(true, 5, 2) = "range(True, 5, 2)"
#py_check range_render.list_str(true, 5, 2) = "[range(True, 5, 2)]"
#py_check range_render.tuple_str(true, 5, 2) = "(range(True, 5, 2),)"
#py_check range_render.dict_str(true, 5, 2) = "{'bounds': range(True, 5, 2)}"
#py_check range_render.stop_numeric(true) =
  (Val.tuple #[.int 1, .list #[.int 0], .tuple #[.int 0]])
#py_check range_render.bounds_numeric(true, 5, 2) =
  (Val.tuple #[.int 2, .list #[.int 1, .int 3], .tuple #[.int 1, .int 3]])
#py_check range_render.index(true, 5, 2, -1) = 3
#py_check range_render.loop_sum(false, 5, true) = 10
#py_check range_render.step_str(false, true, false) raises
  (.valueError "range() arg 3 must not be zero")
#py_check range_render.step_str("bad start", true, false) raises
  (.typeError "'str' object cannot be interpreted as an integer")
#py_check range_render.step_str(true, "bad stop", false) raises
  (.typeError "'str' object cannot be interpreted as an integer")

#guard rangeMake #[] [.bool false, .bool true, .bool true] matches
  .ok (.rangeV (.bool false) (.bool true) (.bool true))
#guard rangeMake #[] [.bool false] matches
  .ok (.rangeV (.int 0) (.bool false) (.int 1))
#guard rangeMake #[] [.bool true, .int 4] matches
  .ok (.rangeV (.bool true) (.int 4) (.int 1))

theorem stop_str_total (value : PyBool) :
    range_render.stop_str(value) ==>
      "range(0, " ++ (if value then "True" else "False") ++ ")" := by proofs

#print axioms stop_str_total
