import Examples.python.float_lab.proof
import LeanModels.Python.Script

open LeanModels LeanModels.Python

load_program float_lab from "Examples/python/float_lab/float_lab.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

#py_check float_lab.tenth() = Float64.ofBits 0x3fb999999999999a
#py_check float_lab.mixed_left() = Val.float (Float64.ofBits 0x4004000000000000)
#py_check float_lab.mixed_right() = Val.float (Float64.ofBits 0x4004000000000000)
#py_check float_lab.integer_true() = Float64.ofBits 0x4004000000000000
#py_check float_lab.signed_zero() = Val.float (Float64.ofBits 0x8000000000000000)
#py_check float_lab.comparisons() =
    Val.tuple #[.bool true, .bool false, .bool true]
#py_check float_lab.truthiness() =
    Val.tuple #[.bool false, .bool false, .bool true]
#py_check float_lab.zero_division() raises .floatZeroDivisionError
#py_check float_lab.conversion_overflow() raises
    .overflowError "int too large to convert to float"
#py_check float_lab.count_head(3, 2) = 3
#py_check float_lab.count_head(true, 1) = 1
#py_check float_lab.count_many() raises
    .typeError "count() takes at most 2 arguments (3 given)"
#py_check float_lab.addition() = Float64.ofBits 0x4008000000000000
#py_check float_lab.augmented() = Float64.ofBits 0xbff4000000000000
#py_check float_lab.mixed_rounding() = Float64.ofBits 0x4340000000000000
#py_check float_lab.cancel(Float64.ofBits 0xbff0000000000000) = Float64.ofBits 0
#py_check float_lab.arithmetic_conversion_error(2) raises
    .overflowError "int too large to convert to float"

theorem tenth :
    float_lab.tenth() ==> Float64.ofBits 0x3fb999999999999a := by proofs

theorem integer_true :
    float_lab.integer_true() ==> Float64.ofBits 0x4004000000000000 := by proofs

theorem default_passthrough (value : PyFloat) :
    float_lab.default(value) ==> value := by proofs

theorem addition :
    float_lab.addition() ==> Float64.ofBits 0x4008000000000000 := by proofs

theorem augmented :
    float_lab.augmented() ==> Float64.ofBits 0xbff4000000000000 := by proofs

theorem mixed_rounding :
    float_lab.mixed_rounding() ==> Float64.ofBits 0x4340000000000000 := by proofs

theorem cancel (value : PyFloat) (finite : value.exponent ≠ 2047) :
    float_lab.cancel(value) ==> Float64.ofBits 0 := by proofs

#print axioms tenth
#print axioms integer_true
#print axioms default_passthrough
#print axioms addition
#print axioms augmented
#print axioms mixed_rounding
#print axioms cancel
