import LeanModels.Python.Float64

set_option maxRecDepth 4096
set_option exponentiation.threshold 2048

namespace LeanModels.Python.Float64.Tests

theorem division_tenth : fromRatio false 1 10 = some (ofBits 0x3fb999999999999a) := rfl

theorem division_two_and_half : fromRatio false 5 2 = some (ofBits 0x4004000000000000) := rfl

theorem negative_zero : fromRatio true 0 2 = some (ofBits 0x8000000000000000) := rfl

theorem half_subnormal_even : fromRatio false 1 (2 ^ 1075) = some (ofBits 0) := rfl

theorem one_and_half_subnormal_even :
    fromRatio false 3 (2 ^ 1075) = some (ofBits 2) := rfl

theorem zero_denominator : fromRatio false 1 0 = none := rfl

theorem integer_division_two_and_half :
    divideInt 5 2 = .ok (ofBits 0x4004000000000000) := rfl

theorem integer_division_negative_zero :
    divideInt 0 (-2) = .ok (ofBits 0x8000000000000000) := rfl

theorem integer_division_by_zero : divideInt 5 0 = .error .zeroDivision := rfl

theorem signed_zeros_equal : (ofBits 0).eqv (ofBits 0x8000000000000000) = true := rfl

theorem nan_is_not_equal : (ofBits 0x7ff8000000000000).eqv (ofBits 0x7ff8000000000000) = false := rfl

theorem float_division_tenth :
    divideFinite (ofBits 0x3ff0000000000000) (ofBits 0x4024000000000000) =
      .ok (ofBits 0x3fb999999999999a) := rfl

theorem float_division_negative_zero :
    divideFinite (ofBits 0) (ofBits 0xc000000000000000) =
      .ok (ofBits 0x8000000000000000) := rfl

theorem float_division_overflow_is_infinity :
    divideFinite (ofBits 0x7fefffffffffffff) (ofBits 0x3fe0000000000000) =
      .ok (ofBits 0x7ff0000000000000) := rfl

theorem mixed_division_converts_before_zero :
    divideIntFloat (10 ^ 400) (ofBits 0) = .error .conversionOverflow := rfl

theorem nan_divided_by_zero :
    divideFinite (ofBits 0x7ff8000000000000) (ofBits 0) = .error .zeroDivision := rfl

theorem equal_large_integer :
    (ofBits 0x4340000000000000).eqInt 9007199254740992 = true := rfl

theorem comparison_does_not_round_integer :
    (ofBits 0x4340000000000000).ltInt 9007199254740993 = true := rfl

theorem negative_zero_not_less : (ofBits 0x8000000000000000).lt (ofBits 0) = false := rfl

theorem nan_not_less : (ofBits 0x7ff8000000000000).lt (ofBits 0x7ff0000000000000) = false := rfl

theorem float_to_integer_truncates_toward_zero :
    (ofBits 0xc004000000000000).toInt = some (-2) := rfl

theorem exact_integer_conversion :
    (ofBits 0x4340000000000000).toIntegralInt = some 9007199254740992 := rfl

theorem fraction_is_not_integral : (ofBits 0x4004000000000000).toIntegralInt = none := rfl

theorem negative_zero_is_integral : (ofBits 0x8000000000000000).toIntegralInt = some 0 := rfl

theorem nan_is_not_integral : (ofBits 0x7ff8000000000000).toIntegralInt = none := rfl

#guard (ofBits 0x3fb999999999999a).repr == some "0.1"
#guard (ofBits 0x4004000000000000).repr == some "2.5"
#guard (ofBits 0x8000000000000000).repr == some "-0.0"
#guard (ofBits 1).repr == some "5e-324"
#guard (ofBits 0x7fefffffffffffff).repr == some "1.7976931348623157e+308"
#guard (ofBits 0x7ff0000000000000).repr == some "inf"
#guard (ofBits 0xfff8000000000001).repr == some "nan"

#print axioms division_tenth
#print axioms division_two_and_half
#print axioms half_subnormal_even
#print axioms one_and_half_subnormal_even
#print axioms integer_division_two_and_half
#print axioms signed_zeros_equal
#print axioms nan_is_not_equal
#print axioms float_division_tenth
#print axioms float_division_negative_zero
#print axioms float_division_overflow_is_infinity
#print axioms mixed_division_converts_before_zero
#print axioms comparison_does_not_round_integer
#print axioms nan_divided_by_zero
#print axioms negative_zero_not_less
#print axioms nan_not_less
#print axioms float_to_integer_truncates_toward_zero
#print axioms exact_integer_conversion
#print axioms fraction_is_not_integral
#print axioms negative_zero_is_integral
#print axioms nan_is_not_integral

theorem addition_tenths :
    arithmetic .add (ofBits 0x3fb999999999999a) (ofBits 0x3fc999999999999a) =
      .ok (ofBits 0x3fd3333333333334) := rfl

theorem negative_zero_sum :
    arithmetic .add (ofBits 0x8000000000000000) (ofBits 0x8000000000000000) =
      .ok (ofBits 0x8000000000000000) := rfl

theorem subtraction_cancels_to_positive_zero :
    arithmetic .sub (ofBits 0xbff0000000000000) (ofBits 0xbff0000000000000) =
      .ok (ofBits 0) := rfl

theorem negative_zero_difference :
    arithmetic .sub (ofBits 0x8000000000000000) (ofBits 0) =
      .ok (ofBits 0x8000000000000000) := rfl

theorem addition_half_ulp_even :
    arithmetic .add (ofBits 0x3ff0000000000000) (ofBits 0x3ca0000000000000) =
      .ok (ofBits 0x3ff0000000000000) := rfl

theorem addition_half_ulp_odd :
    arithmetic .add (ofBits 0x3ff0000000000001) (ofBits 0x3ca0000000000000) =
      .ok (ofBits 0x3ff0000000000002) := rfl

theorem multiplication_subnormal_even :
    arithmetic .mult (ofBits 1) (ofBits 0x3fe0000000000000) = .ok (ofBits 0) := rfl

theorem multiplication_subnormal_odd :
    arithmetic .mult (ofBits 3) (ofBits 0x3fe0000000000000) = .ok (ofBits 2) := rfl

theorem multiplication_overflows_to_infinity :
    arithmetic .mult (ofBits 0x7fefffffffffffff) (ofBits 0x4000000000000000) =
      .ok (ofBits 0x7ff0000000000000) := rfl

theorem indeterminate_infinity_requires_nan_oracle :
    arithmetic .sub (ofBits 0x7ff0000000000000) (ofBits 0x7ff0000000000000) =
      .error .nanPayload := rfl

theorem mixed_arithmetic_converts_before_nan :
    arithmeticIntFloat .add (10 ^ 400) (ofBits 0x7ff8000000000001) =
      .error .conversionOverflow := rfl

#print axioms addition_tenths
#print axioms negative_zero_sum
#print axioms subtraction_cancels_to_positive_zero
#print axioms negative_zero_difference
#print axioms addition_half_ulp_even
#print axioms addition_half_ulp_odd
#print axioms multiplication_subnormal_even
#print axioms multiplication_subnormal_odd
#print axioms multiplication_overflows_to_infinity
#print axioms indeterminate_infinity_requires_nan_oracle
#print axioms mixed_arithmetic_converts_before_nan
#print axioms arithmetic_sub_self

end LeanModels.Python.Float64.Tests
