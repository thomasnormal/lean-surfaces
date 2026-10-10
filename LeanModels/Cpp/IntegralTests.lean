import LeanModels.Cpp.Integral

namespace LeanModels.Cpp.IntegralTests

def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩
def unsigned (value : Int) : IntegralValue := ⟨.unsigned 32, value⟩

#guard integralConvert (.signed 8) (unsigned 255) == .ok ⟨.signed 8, -1⟩
#guard integralConvert (.unsigned 8) (signed (-257)) == .ok ⟨.unsigned 8, 255⟩
#guard integralConvert .boolean (signed (-1)) == .ok ⟨.boolean, 1⟩
#guard integralConvert .boolean (signed 0) == .ok ⟨.boolean, 0⟩
#guard integralConvert (.signed 32) ⟨.boolean, 1⟩ == .ok (signed 1)
#guard integralConvert (.signed 0) (signed 0) == .invalid .zeroWidth
#guard integralConvert (.unsigned 8) ⟨.signed 0, 0⟩ == .invalid .zeroWidth
#guard integralConvert (.unsigned 8) ⟨.boolean, 2⟩ == .invalid .outOfRange
#guard integralUnary .plus (signed (-3)) == .ok (signed (-3))
#guard integralUnary .negate (signed (-2147483648)) == .undefined .signedOverflow
#guard integralUnary .negate (unsigned 1) == .ok (unsigned 4294967295)
#guard integralUnary .complement (signed (-1)) == .ok (signed 0)
#guard integralUnary .complement (unsigned 0) == .ok (unsigned 4294967295)
#guard integralUnary .logicalNot ⟨.boolean, 0⟩ == .ok ⟨.boolean, 1⟩
#guard integralUnary .logicalNot (signed (-3)) == .ok ⟨.boolean, 0⟩
#guard integralUnary .plus ⟨.boolean, 1⟩ == .unsupported .unpromotedBoolean
#guard integralUnary .negate ⟨.unsigned 8, 256⟩ == .invalid .outOfRange
#guard integralBinary .add (signed 2147483647) (signed 1) == .undefined .signedOverflow
#guard integralBinary .subtract (signed (-2147483648)) (signed 1) == .undefined .signedOverflow
#guard integralBinary .multiply (signed 1073741824) (signed 2) == .undefined .signedOverflow
#guard integralBinary .add (unsigned 4294967295) (unsigned 1) == .ok (unsigned 0)
#guard integralBinary .subtract (unsigned 0) (unsigned 1) == .ok (unsigned 4294967295)
#guard integralBinary .multiply (unsigned 4294967295) (unsigned 2) == .ok (unsigned 4294967294)
#guard integralBinary .divide (signed (-7)) (signed 3) == .ok (signed (-2))
#guard integralBinary .remainder (signed (-7)) (signed 3) == .ok (signed (-1))
#guard integralBinary .divide (signed 7) (signed (-3)) == .ok (signed (-2))
#guard integralBinary .remainder (signed 7) (signed (-3)) == .ok (signed 1)
#guard integralBinary .divide (signed 1) (signed 0) == .undefined .divisionByZero
#guard integralBinary .remainder (unsigned 1) (unsigned 0) == .undefined .divisionByZero
#guard integralBinary .divide (signed (-2147483648)) (signed (-1)) == .undefined .divisionOverflow
#guard integralBinary .remainder (signed (-2147483648)) (signed (-1)) == .undefined .divisionOverflow
#guard integralBinary .shiftLeft (signed (-1)) (signed 1) == .ok (signed (-2))
#guard integralBinary .shiftLeft (signed 1) (signed 31) == .ok (signed (-2147483648))
#guard integralBinary .shiftLeft (signed (-2147483648)) (signed 1) == .ok (signed 0)
#guard integralBinary .shiftRight (signed (-7)) (signed 1) == .ok (signed (-4))
#guard integralBinary .shiftRight (unsigned 4294967295) (signed 1) == .ok (unsigned 2147483647)
#guard integralBinary .shiftLeft (signed 1) (signed (-1)) == .undefined .negativeShift
#guard integralBinary .shiftRight (signed 1) (unsigned 32) == .undefined .excessiveShift
#guard integralBinary .shiftLeft (signed 1) ⟨.unsigned 64, 31⟩ == .ok (signed (-2147483648))
#guard integralBinary .bitAnd (signed (-3)) (signed 6) == .ok (signed 4)
#guard integralBinary .bitOr (signed (-3)) (signed 6) == .ok (signed (-1))
#guard integralBinary .bitXor (signed (-3)) (signed 6) == .ok (signed (-5))
#guard integralBinary .equal (signed (-1)) (signed (-1)) == .ok ⟨.boolean, 1⟩
#guard integralBinary .notEqual (signed (-1)) (signed 1) == .ok ⟨.boolean, 1⟩
#guard integralBinary .less (signed (-1)) (signed 0) == .ok ⟨.boolean, 1⟩
#guard integralBinary .lessEqual (signed 0) (signed 0) == .ok ⟨.boolean, 1⟩
#guard integralBinary .greater (unsigned 4294967295) (unsigned 0) == .ok ⟨.boolean, 1⟩
#guard integralBinary .greaterEqual (signed 0) (signed 0) == .ok ⟨.boolean, 1⟩
#guard integralBinary .add (signed (-1)) (unsigned 1) == .unsupported .unresolvedArithmeticConversions
#guard integralBinary .equal ⟨.boolean, 1⟩ ⟨.boolean, 1⟩ == .unsupported .unpromotedBoolean
#guard integralBinary .add (signed 1) ⟨.signed 32, 2147483648⟩ == .invalid .outOfRange
#guard integralBinary .shiftRight ⟨.unsigned 0, 0⟩ (signed 1) == .invalid .zeroWidth
#guard integralConvert (.signed 64) ⟨.unsigned 64, 18446744073709551615⟩ ==
  .ok ⟨.signed 64, -1⟩
#guard integralConvert (.unsigned 64) ⟨.signed 64, -1⟩ ==
  .ok ⟨.unsigned 64, 18446744073709551615⟩
#guard integralBinary .add ⟨.unsigned 64, 18446744073709551615⟩ ⟨.unsigned 64, 1⟩ ==
  .ok ⟨.unsigned 64, 0⟩
#guard integralBinary .shiftLeft ⟨.signed 64, 1⟩ (unsigned 63) ==
  .ok ⟨.signed 64, -9223372036854775808⟩
#guard integralBinary .shiftRight ⟨.signed 64, -9223372036854775808⟩ (signed 63) ==
  .ok ⟨.signed 64, -1⟩
#guard integralBinary .remainder ⟨.signed 64, -9223372036854775808⟩ ⟨.signed 64, -1⟩ ==
  .undefined .divisionOverflow

set_option maxRecDepth 4096

#guard_expr integralBinary .bitAnd ⟨.signed 64, -3⟩ ⟨.signed 64, 6⟩ =~
  (IntegralResult.ok ⟨.signed 64, 4⟩)
#guard_expr integralBinary .bitOr ⟨.signed 64, -3⟩ ⟨.signed 64, 6⟩ =~
  (IntegralResult.ok ⟨.signed 64, -1⟩)
#guard_expr integralBinary .bitXor ⟨.signed 64, -3⟩ ⟨.signed 64, 6⟩ =~
  (IntegralResult.ok ⟨.signed 64, -5⟩)
#guard_expr integralBinary .shiftRight ⟨.signed 64, -7⟩ (signed 1) =~
  (IntegralResult.ok ⟨.signed 64, -4⟩)
#guard_expr integralConvert (.signed 64) ⟨.unsigned 64, 18446744073709551615⟩ =~
  (IntegralResult.ok ⟨.signed 64, -1⟩)

end LeanModels.Cpp.IntegralTests
