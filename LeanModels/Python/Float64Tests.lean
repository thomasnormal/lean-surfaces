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

end LeanModels.Python.Float64.Tests
