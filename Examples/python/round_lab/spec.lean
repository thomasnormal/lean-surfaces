import Examples.python.round_lab.proof
import LeanModels.Python.Script

open LeanModels LeanModels.Python

load_program round_lab from "Examples/python/round_lab/round_lab.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

#py_check round_lab.round_float_ties() =
  Val.tuple #[.int 0, .int 2, .int 2, .int 0, .int (-2), .int (-2)]
#py_check round_lab.round_float_nan() raises
  (.valueError "cannot convert float NaN to integer")
#py_check round_lab.round_float_infinity() raises
  (.overflowError "cannot convert float infinity to integer")
#py_check round_lab.round_float_zero(Float64.ofBits 0x3ff8000000000000) =
  Val.float (Float64.ofBits 0x4000000000000000)
#py_check round_lab.round_int_zero(7) = 7
#py_check round_lab.round_bool_zero(true) = 1
#py_check round_lab.round_int_positive(7) = 7
#py_check round_lab.round_bool_positive(true) = 1
