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
#py_check round_lab.round_float_one(Float64.ofBits 0x4005666666666666) =
  Val.float (Float64.ofBits 0x400599999999999a)
#py_check round_lab.round_float_two(Float64.ofBits 0x3ff3c083126e978d) =
  Val.float (Float64.ofBits 0x3ff3ae147ae147ae)
#py_check round_lab.round_float_three(Float64.ofBits 0x3ff3c083126e978d) =
  Val.float (Float64.ofBits 0x3ff3be76c8b43958)
#py_check round_lab.round_float_four(Float64.ofBits 0x3ff3c0c1fc8f3238) =
  Val.float (Float64.ofBits 0x3ff3c0ebedfa43fe)
#py_check round_lab.round_float_five(Float64.ofBits 0x3ff3c0c9539b8887) =
  Val.float (Float64.ofBits 0x3ff3c0cc78e9f6a9)
#py_check round_lab.round_float_six(Float64.ofBits 0x3ff3c0ca2a5b1d5d) =
  Val.float (Float64.ofBits 0x3ff3c0ca600b0293)
#py_check round_lab.round_float_seven(Float64.ofBits 0x3ff3c0ca4283de1b) =
  Val.float (Float64.ofBits 0x3ff3c0ca45330ff8)
#py_check round_lab.round_float_eight(Float64.ofBits 0x3ff3c0ca43db770a) =
  Val.float (Float64.ofBits 0x3ff3c0ca45330ff8)
