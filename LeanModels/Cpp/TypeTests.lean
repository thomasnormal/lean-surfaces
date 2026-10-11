import LeanModels.Cpp.Types

namespace LeanModels.Cpp.TypeTests

open LeanModels.Cpp

def p : TargetProfile := TargetProfile.lp64

def formatResult (result : Except TypeResolutionError IntegralFormat) (expected : IntegralFormat) : Bool :=
  match result with
  | .ok actual => actual == expected
  | .error _ => false

def typeResult (result : Except TypeResolutionError CppIntType) (expected : CppIntType) : Bool :=
  match result with
  | .ok actual => actual == expected
  | .error _ => false

def formatError (result : Except TypeResolutionError IntegralFormat) (expected : TypeResolutionError) : Bool :=
  match result with
  | .error actual => actual == expected
  | .ok _ => false

def resolvedResult (result : Except TypeResolutionError (CppIntType × IntegralFormat))
    (expectedType : CppIntType) (expectedFormat : IntegralFormat) : Bool :=
  match result with
  | .ok (actualType, actualFormat) => actualType == expectedType && actualFormat == expectedFormat
  | .error _ => false

def tiny : TargetProfile := {
  charWidth := 8
  shortWidth := 16
  intWidth := 16
  longWidth := 32
  longLongWidth := 64
  charSigned := false
}

#guard p.valid
#guard formatResult (p.format .boolean) .boolean
#guard formatResult (p.format .char) (.signed 8)
#guard formatResult (({p with charSigned := false}).format .char) (.unsigned 8)
#guard formatResult (p.format .signedChar) (.signed 8)
#guard formatResult (p.format .unsignedShort) (.unsigned 16)
#guard formatResult (p.format .longLong) (.signed 64)
#guard !({p with intWidth := 0}).valid
#guard !({p with charWidth := 7}).valid
#guard !({p with shortWidth := 15}).valid
#guard !({p with intWidth := 15}).valid
#guard !({p with longWidth := 31}).valid
#guard !({p with longLongWidth := 63}).valid
#guard tiny.valid
#guard formatError (({p with intWidth := 0}).format .int) .invalidProfile
#guard typeResult (integralPromotion p .boolean) .int
#guard typeResult (integralPromotion p .char) .int
#guard typeResult (integralPromotion p .signedChar) .int
#guard typeResult (integralPromotion p .unsignedChar) .int
#guard typeResult (integralPromotion p .short) .int
#guard typeResult (integralPromotion p .unsignedShort) .int
#guard typeResult (integralPromotion p .int) .int
#guard typeResult (integralPromotion p .unsignedInt) .unsignedInt
#guard typeResult (integralPromotion p .long) .long
#guard typeResult (integralPromotion p .unsignedLongLong) .unsignedLongLong
#guard typeResult (integralPromotion tiny .unsignedShort) .unsignedInt
#guard typeResult (integralPromotion tiny .char) .int
#guard typeResult (integralPromotion tiny .unsignedChar) .int
#guard typeResult (usualArithmeticType p .boolean .int) .int
#guard typeResult (usualArithmeticType p .char .unsignedChar) .int
#guard typeResult (usualArithmeticType p .short .unsignedShort) .int
#guard typeResult (usualArithmeticType p .int .unsignedInt) .unsignedInt
#guard typeResult (usualArithmeticType p .int .long) .long
#guard typeResult (usualArithmeticType p .unsignedInt .long) .long
#guard typeResult (usualArithmeticType p .unsignedLong .longLong) .unsignedLongLong
#guard typeResult (usualArithmeticType p .long .unsignedLong) .unsignedLong
#guard typeResult (usualArithmeticType p .long .unsignedInt) .long
#guard typeResult (usualArithmeticType p .longLong .unsignedLong) .unsignedLongLong
#guard typeResult (usualArithmeticType p .unsignedChar .short) .int
#guard typeResult (usualArithmeticType p .unsignedLongLong .longLong) .unsignedLongLong
#guard typeResult (usualArithmeticType tiny .unsignedShort .int) .unsignedInt
#guard typeResult (usualArithmeticType tiny .unsignedInt .long) .long
#guard resolvedResult (resolveArithmeticFormats p .short .unsignedInt) .unsignedInt (.unsigned 32)
#guard resolvedResult (resolveArithmeticFormats p .long .unsignedInt) .long (.signed 64)
#guard resolvedResult (resolveArithmeticFormats p .unsignedLong .longLong) .unsignedLongLong (.unsigned 64)
#guard CppIntType.rank .char == CppIntType.rank .unsignedChar
#guard CppIntType.rank .short < CppIntType.rank .int
#guard CppIntType.unsignedCounterpart .long == some .unsignedLong
#guard CppIntType.unsignedCounterpart .unsignedLong == none
#guard CppIntType.signedCounterpart .unsignedInt == some .int
#guard CppIntType.signedCounterpart .long == none

end LeanModels.Cpp.TypeTests
