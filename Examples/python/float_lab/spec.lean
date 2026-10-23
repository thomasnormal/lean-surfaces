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
#py_check float_lab.attribute_still_loud() = true
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
#py_check float_lab.count_prefix(1, Float64.ofBits 0x3fe0000000000000) =
  Val.tuple #[.int 1, .float (Float64.ofBits 0x3ff8000000000000),
    .float (Float64.ofBits 0x4000000000000000)]
#py_check float_lab.count_prefix(true, 2) =
  Val.tuple #[.bool true, .int 3, .int 5]
#py_check float_lab.count_prefix(false, 0) =
  Val.tuple #[.bool false, .int 0, .int 0]
#py_check float_lab.count_many() raises
    .typeError "count() takes at most 2 arguments (3 given)"
#py_check float_lab.addition() = Float64.ofBits 0x4008000000000000
#py_check float_lab.augmented() = Float64.ofBits 0xbff4000000000000
#py_check float_lab.mixed_rounding() = Float64.ofBits 0x4340000000000000
#py_check float_lab.cancel(Float64.ofBits 0xbff0000000000000) = Float64.ofBits 0
#py_check float_lab.arithmetic_conversion_error(2) raises
    .overflowError "int too large to convert to float"
#py_check float_lab.constructor_zero() = Float64.ofBits 0
#py_check float_lab.constructor_tenth() = Float64.ofBits 0x3fb999999999999a
#py_check float_lab.constructor_unicode() = Float64.ofBits 0x3fb999999999999a
#py_check float_lab.constructor("nan") = Float64.ofBits 0x7ff8000000000000
#py_check float_lab.constructor("-NaN") = Float64.ofBits 0xfff8000000000000
#py_check float_lab.constructor("+nAn") = Float64.ofBits 0x7ff8000000000000
#py_check float_lab.constructor_rounding() = Float64.ofBits 0x4340000000000000
#py_check float_lab.constructor_invalid_caught() = 17
#py_check float_lab.constructor_many() raises
    .typeError "float expected at most 1 argument, got 2"
#py_check float_lab.constructor_bad_then_many() raises
    .typeError "float expected at most 1 argument, got 2"
#py_check float_lab.constructor_order() raises .zeroDivisionError
#py_check float_lab.constructor("1._0") raises
    .valueError "could not convert string to float: '1._0'"
#py_check float_lab.constructor_overflow() raises
    .overflowError "int too large to convert to float"
#py_check float_lab.constructor_shadow() = 8
#py_check float_lab.constructor_keyword() raises
  (.typeError "float() takes no keyword arguments")
#py_check float_lab.nonfinite_division_still_loud() = Float64.ofBits 0x7ff0000000000000
#py_check float_lab.infinite_quotient() = Float64.ofBits 0xfff0000000000000
#py_check float_lab.infinite_denominator() = Float64.ofBits 0x8000000000000000
#py_check float_lab.infinite_augmented() = Float64.ofBits 0
#py_check float_lab.infinite_zero_caught() = 19
#py_check float_lab.floor_tenth() = Float64.ofBits 0x4022000000000000
#py_check float_lab.remainder_tenth() = Float64.ofBits 0x3fb9999999999996
#py_check float_lab.floor_infinite() = Float64.ofBits 0xbff0000000000000
#py_check float_lab.remainder_infinite() = Float64.ofBits 0xfff0000000000000
#py_check float_lab.floor_augmented() = Float64.ofBits 0x3ff0000000000000
#py_check float_lab.floor_zero(0) raises .floatFloorZeroDivisionError
#py_check float_lab.floor_zero(1) raises .floatModuloZeroDivisionError
#py_check float_lab.floor_zero(2) raises .floatDivmodZeroDivisionError
#py_check float_lab.floor_zero_caught(2) = 23
#py_check float_lab.division_nonfinite_overflow(0) raises
    .overflowError "int too large to convert to float"
#py_check float_lab.division_nonfinite_overflow(1) raises
    .overflowError "int too large to convert to float"
#py_check float_lab.divide(Float64.ofBits 0x7ff0000000000001, false) raises
    .floatZeroDivisionError

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

theorem constructor_identity (value : PyFloat) :
    float_lab.constructor(value) ==> value := by proofs

theorem constructor_zero :
    float_lab.constructor_zero() ==> Float64.ofBits 0 := by proofs

theorem constructor_tenth :
    float_lab.constructor_tenth() ==> Float64.ofBits 0x3fb999999999999a := by proofs

theorem constructor_unicode :
    float_lab.constructor_unicode() ==> Float64.ofBits 0x3fb999999999999a := by proofs

theorem constructor_rounding :
    float_lab.constructor_rounding() ==> Float64.ofBits 0x4340000000000000 := by proofs

theorem constructor_invalid_caught :
    float_lab.constructor_invalid_caught() ==> (17 : PyInt) := by proofs

theorem infinity_literal :
    float_lab.nonfinite_division_still_loud() ==> Float64.ofBits 0x7ff0000000000000 := by proofs

theorem infinite_quotient :
    float_lab.infinite_quotient() ==> Float64.ofBits 0xfff0000000000000 := by proofs

theorem infinite_denominator :
    float_lab.infinite_denominator() ==> Float64.ofBits 0x8000000000000000 := by proofs

theorem infinite_augmented :
    float_lab.infinite_augmented() ==> Float64.ofBits 0 := by proofs

theorem infinite_zero_caught :
    float_lab.infinite_zero_caught() ==> (19 : PyInt) := by proofs

theorem floor_tenth :
    float_lab.floor_tenth() ==> Float64.ofBits 0x4022000000000000 := by proofs

theorem remainder_tenth :
    float_lab.remainder_tenth() ==> Float64.ofBits 0x3fb9999999999996 := by proofs

theorem floor_infinite :
    float_lab.floor_infinite() ==> Float64.ofBits 0xbff0000000000000 := by proofs

theorem remainder_infinite :
    float_lab.remainder_infinite() ==> Float64.ofBits 0xfff0000000000000 := by proofs

theorem floor_augmented :
    float_lab.floor_augmented() ==> Float64.ofBits 0x3ff0000000000000 := by proofs

theorem floor_zero_caught :
    float_lab.floor_zero_caught(2) ==> (23 : PyInt) := by proofs

#print axioms floor_tenth
#print axioms remainder_tenth
#print axioms floor_infinite
#print axioms remainder_infinite
#print axioms floor_augmented
#print axioms floor_zero_caught
#print axioms infinity_literal
#print axioms infinite_quotient
#print axioms infinite_denominator
#print axioms infinite_augmented
#print axioms infinite_zero_caught
#print axioms constructor_identity
#print axioms constructor_zero
#print axioms constructor_tenth
#print axioms constructor_unicode
#print axioms constructor_rounding
#print axioms constructor_invalid_caught
#print axioms tenth
#print axioms integer_true
#print axioms default_passthrough
#print axioms addition
#print axioms augmented
#print axioms mixed_rounding
#print axioms cancel
