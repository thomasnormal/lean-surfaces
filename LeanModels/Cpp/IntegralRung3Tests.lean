import LeanModels.Cpp.Integral

namespace LeanModels.Cpp.IntegralRung3Tests

def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩
def boolean (value : Int) : IntegralValue := ⟨.boolean, value⟩

def integralExpressionWitness : Bool :=
  integralBinary .add (signed 7) (signed 5) == .ok (signed 12) &&
    integralBinary .divide (signed (-7)) (signed 3) == .ok (signed (-2)) &&
    integralBinary .remainder (signed (-7)) (signed 3) == .ok (signed (-1)) &&
    integralBinary .bitAnd (signed (-3)) (signed 6) == .ok (signed 4) &&
    integralBinary .equal (signed 12) (signed 12) == .ok (boolean 1) &&
    integralBinary .add (signed 2147483647) (signed 1) ==
      .undefined .signedOverflow &&
    integralBinary .divide (signed 1) (signed 0) ==
      .undefined .divisionByZero

def integralUnaryShiftWitness : Bool :=
  integralUnary .negate (signed 3) == .ok (signed (-3)) &&
    integralUnary .complement (signed (-1)) == .ok (signed 0) &&
    integralUnary .logicalNot (signed (-3)) == .ok (boolean 0) &&
    integralBinary .shiftLeft (signed 1) (signed 3) == .ok (signed 8) &&
    integralBinary .shiftRight (signed (-7)) (signed 1) == .ok (signed (-4)) &&
    integralBinary .shiftLeft (signed 1) (signed 32) == .undefined .excessiveShift

#guard integralExpressionWitness
#guard integralUnaryShiftWitness

theorem integral_expression_witness : integralExpressionWitness = true := by
  rfl

theorem integral_unary_shift_witness : integralUnaryShiftWitness = true := by
  rfl

#print axioms integral_expression_witness
#print axioms integral_unary_shift_witness

end LeanModels.Cpp.IntegralRung3Tests
