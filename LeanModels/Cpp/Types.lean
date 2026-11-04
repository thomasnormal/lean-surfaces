import LeanModels.Cpp.Integral

namespace LeanModels.Cpp

inductive CppIntType where
  | boolean
  | char
  | signedChar
  | unsignedChar
  | short
  | unsignedShort
  | int
  | unsignedInt
  | long
  | unsignedLong
  | longLong
  | unsignedLongLong
  deriving Repr, BEq, Inhabited

inductive TypeResolutionError where
  | invalidProfile
  | unsupportedType (type : CppIntType)
  deriving Repr, BEq, Inhabited

structure TargetProfile where
  charWidth : Nat
  shortWidth : Nat
  intWidth : Nat
  longWidth : Nat
  longLongWidth : Nat
  charSigned : Bool
  deriving Repr, BEq, Inhabited

namespace TargetProfile

def lp64 : TargetProfile := {
  charWidth := 8
  shortWidth := 16
  intWidth := 32
  longWidth := 64
  longLongWidth := 64
  charSigned := true
}

def valid (profile : TargetProfile) : Bool :=
  profile.charWidth ≥ 8 && profile.shortWidth ≥ 16 && profile.intWidth ≥ 16 &&
    profile.longWidth ≥ 32 && profile.longLongWidth ≥ 64 &&
    profile.shortWidth ≥ profile.charWidth && profile.intWidth ≥ profile.shortWidth &&
    profile.longWidth ≥ profile.intWidth && profile.longLongWidth ≥ profile.longWidth

private def signedFormat (width : Nat) : IntegralFormat := .signed width
private def unsignedFormat (width : Nat) : IntegralFormat := .unsigned width

def format? (profile : TargetProfile) (type : CppIntType) : Option IntegralFormat :=
  match type with
  | .boolean => some .boolean
  | .char => some (if profile.charSigned then signedFormat profile.charWidth
      else unsignedFormat profile.charWidth)
  | .signedChar => some (signedFormat profile.charWidth)
  | .unsignedChar => some (unsignedFormat profile.charWidth)
  | .short => some (signedFormat profile.shortWidth)
  | .unsignedShort => some (unsignedFormat profile.shortWidth)
  | .int => some (signedFormat profile.intWidth)
  | .unsignedInt => some (unsignedFormat profile.intWidth)
  | .long => some (signedFormat profile.longWidth)
  | .unsignedLong => some (unsignedFormat profile.longWidth)
  | .longLong => some (signedFormat profile.longLongWidth)
  | .unsignedLongLong => some (unsignedFormat profile.longLongWidth)

def format (profile : TargetProfile) (type : CppIntType) :
    Except TypeResolutionError IntegralFormat :=
  if !profile.valid then .error .invalidProfile
  else match profile.format? type with
    | some format => .ok format
    | none => .error (.unsupportedType type)

end TargetProfile

namespace CppIntType

def rank : CppIntType → Nat
  | .boolean => 0
  | .char | .signedChar | .unsignedChar => 1
  | .short | .unsignedShort => 2
  | .int | .unsignedInt => 3
  | .long | .unsignedLong => 4
  | .longLong | .unsignedLongLong => 5

def isSigned : CppIntType → Bool
  | .boolean | .unsignedChar | .unsignedShort | .unsignedInt | .unsignedLong |
      .unsignedLongLong => false
  | _ => true

def isUnsigned (type : CppIntType) : Bool :=
  type != .boolean && !type.isSigned

def unsignedCounterpart : CppIntType → Option CppIntType
  | .signedChar | .char => some .unsignedChar
  | .short => some .unsignedShort
  | .int => some .unsignedInt
  | .long => some .unsignedLong
  | .longLong => some .unsignedLongLong
  | .unsignedChar | .unsignedShort | .unsignedInt | .unsignedLong |
      .unsignedLongLong => none
  | .boolean => none

def signedCounterpart : CppIntType → Option CppIntType
  | .unsignedChar | .char => some .signedChar
  | .unsignedShort => some .short
  | .unsignedInt => some .int
  | .unsignedLong => some .long
  | .unsignedLongLong => some .longLong
  | .signedChar | .short | .int | .long | .longLong | .boolean => none

end CppIntType

private def allValuesRepresentable (profile : TargetProfile)
    (signedType unsignedType : CppIntType) : Bool :=
  match profile.format signedType, profile.format unsignedType with
  | .ok signedFormat, .ok unsignedFormat =>
      signedFormat.maximum ≥ unsignedFormat.maximum
  | _, _ => false

private def promotedNarrowType (profile : TargetProfile) (type : CppIntType) :
    Except TypeResolutionError CppIntType := do
  let intFormat ← profile.format .int
  let sourceFormat ← profile.format type
  if intFormat.maximum ≥ sourceFormat.maximum then
    .ok .int
  else
    .ok .unsignedInt

def integralPromotion (profile : TargetProfile) (type : CppIntType) :
    Except TypeResolutionError CppIntType := do
  let _ ← profile.format type
  match type with
  | .boolean | .char | .signedChar | .unsignedChar | .short | .unsignedShort =>
      promotedNarrowType profile type
  | _ => .ok type

def usualArithmeticType (profile : TargetProfile)
    (left right : CppIntType) : Except TypeResolutionError CppIntType := do
  let left ← integralPromotion profile left
  let right ← integralPromotion profile right
  if left == right then return left
  if left.isSigned == right.isSigned then
    return if left.rank ≥ right.rank then left else right
  let unsignedType := if left.isUnsigned then left else right
  let signedType := if left.isSigned then left else right
  if unsignedType.rank ≥ signedType.rank then return unsignedType
  if allValuesRepresentable profile signedType unsignedType then return signedType
  match signedType.unsignedCounterpart with
  | some counterpart => return counterpart
  | none => .error .invalidProfile

def resolveArithmeticFormats (profile : TargetProfile)
    (left right : CppIntType) :
    Except TypeResolutionError (CppIntType × IntegralFormat) := do
  let type ← usualArithmeticType profile left right
  return (type, ← profile.format type)

end LeanModels.Cpp
