import Examples.python.decimal_render.proof

open LeanModels LeanModels.Python

load_program decimal_render from "Examples/python/decimal_render/decimal_render.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 4300

#py_check decimal_render.scalar_str(0) = "0"
#py_check decimal_render.scalar_str(-27) = "-27"
#py_check decimal_render.scalar_str(true) = "True"
#py_check decimal_render.scalar_str(false) = "False"
#py_check decimal_render.format_s(-27) = "-27"
#py_check decimal_render.format_r(-27) = "-27"
#py_check decimal_render.format_r("hé") = "'hé'"
#py_check decimal_render.format_d(-27) = "-27"
#py_check decimal_render.format_d(true) = "1"
#py_check decimal_render.format_d(false) = "0"
#py_check decimal_render.tuple_str(-27) = "(-27,)"
#py_check decimal_render.list_str(-27) = "[-27]"
#py_check decimal_render.dict_key_str(-27) = "{-27: 7}"
#py_check decimal_render.dict_value_str(-27) = "{'value': -27}"
#py_check decimal_render.range_stop_str(-27) = "range(0, -27)"
#py_check decimal_render.range_start_str(-27) = "range(-27, -27)"
#py_check decimal_render.range_step_str(-27) = "range(0, 2, -27)"
#py_check decimal_render.namedtuple_str(-27) = "Pair(x=-27, y=7)"
#py_check decimal_render.tuple_str("hé") = "('hé',)"
#py_check decimal_render.list_str("hé") = "['hé']"
#py_check decimal_render.dict_key_str("hé") = "{'hé': 7}"
#py_check decimal_render.dict_value_str("hé") = "{'value': 'hé'}"
#py_check decimal_render.namedtuple_str("hé") = "Pair(x='hé', y=7)"
#py_check decimal_render.fstring_str(-27) = "-27"

#guard intDecimal ((10 : Int) ^ 4300 - 1) matches some _
#guard intDecimal (-((10 : Int) ^ 4300 - 1)) matches some _
#guard intDecimal ((10 : Int) ^ 4300) matches none
#guard intDecimal (-((10 : Int) ^ 4300)) matches none
#guard intDecimal ((10 : Int) ^ 4301) matches none
#guard intDecimal (-((10 : Int) ^ 4301)) matches none

theorem scalar_str_total (value : PyInt)
    (valueBound : value.natAbs < 10 ^ 4300) :
    decimal_render.scalar_str(value) ==> toString value := by proofs

#print axioms scalar_str_total
