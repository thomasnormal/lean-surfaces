import LeanModels.Cpp.Types

namespace LeanModels.Cpp

inductive CppCharacterType where
  | wchar
  | char8
  | char16
  | char32
  deriving Repr, BEq, Inhabited

inductive CppFloatingType where
  | float
  | double
  | longDouble
  deriving Repr, BEq, Inhabited

inductive CppScalarType where
  | void
  | integral (type : CppIntType)
  | character (type : CppCharacterType)
  | floating (type : CppFloatingType)
  deriving Repr, BEq, Inhabited

def CppScalarType.isObject : CppScalarType → Bool
  | .void => false
  | _ => true

def CppScalarType.isIntegral : CppScalarType → Bool
  | .integral _ | .character _ => true
  | _ => false

def CppScalarType.isFloating : CppScalarType → Bool
  | .floating _ => true
  | _ => false

def CppScalarType.isArithmetic : CppScalarType → Bool
  | .integral _ | .character _ | .floating _ => true
  | .void => false

structure CvQualifiers where
  isConst : Bool
  isVolatile : Bool
  deriving Repr, BEq, Inhabited

namespace CvQualifiers

def none : CvQualifiers := {isConst := false, isVolatile := false}

def isUnqualified (qualifiers : CvQualifiers) : Bool :=
  !qualifiers.isConst && !qualifiers.isVolatile

end CvQualifiers

structure CppQualifiedScalar where
  base : CppScalarType
  cv : CvQualifiers
  deriving Repr, BEq, Inhabited

namespace CppQualifiedScalar

def unqualified (base : CppScalarType) : CppQualifiedScalar :=
  {base, cv := .none}

def addConst (type : CppQualifiedScalar) : CppQualifiedScalar :=
  {type with cv.isConst := true}

def addVolatile (type : CppQualifiedScalar) : CppQualifiedScalar :=
  {type with cv.isVolatile := true}

def removeCv (type : CppQualifiedScalar) : CppQualifiedScalar :=
  unqualified type.base

def sameUnqualified (left right : CppQualifiedScalar) : Bool :=
  left.base == right.base

def isObject (type : CppQualifiedScalar) : Bool := type.base.isObject

def isIntegral (type : CppQualifiedScalar) : Bool := type.base.isIntegral

def isFloating (type : CppQualifiedScalar) : Bool := type.base.isFloating

def isArithmetic (type : CppQualifiedScalar) : Bool := type.base.isArithmetic

end CppQualifiedScalar

structure ScalarProfile where
  integers : TargetProfile
  wcharWidth : Nat
  char8Width : Nat
  char16Width : Nat
  char32Width : Nat
  floatWidth : Nat
  doubleWidth : Nat
  longDoubleWidth : Nat
  deriving Repr, BEq, Inhabited

namespace ScalarProfile

def lp64 : ScalarProfile := {
  integers := .lp64
  wcharWidth := 32
  char8Width := 8
  char16Width := 16
  char32Width := 32
  floatWidth := 32
  doubleWidth := 64
  longDoubleWidth := 80
}

def valid (profile : ScalarProfile) : Bool :=
  profile.integers.valid && profile.char8Width == 8 &&
    profile.char16Width ≥ 16 && profile.char32Width ≥ profile.char16Width &&
    profile.wcharWidth ≥ 16 && profile.floatWidth ≥ 32 &&
    profile.doubleWidth ≥ profile.floatWidth &&
    profile.longDoubleWidth ≥ profile.doubleWidth

end ScalarProfile

inductive ScalarWidthError where
  | invalidProfile
  | voidType
  deriving Repr, BEq, Inhabited

def scalarWidthBits (profile : ScalarProfile) (type : CppScalarType) :
    Except ScalarWidthError Nat :=
  if !profile.valid then .error .invalidProfile
  else match type with
    | .void => .error .voidType
    | .integral integer =>
        match profile.integers.format integer with
        | .ok format => .ok (IntegralFormat.width format)
        | .error _ => .error .invalidProfile
    | .character character => .ok (match character with
        | .wchar => profile.wcharWidth
        | .char8 => profile.char8Width
        | .char16 => profile.char16Width
        | .char32 => profile.char32Width)
    | .floating floating => .ok (match floating with
        | .float => profile.floatWidth
        | .double => profile.doubleWidth
        | .longDouble => profile.longDoubleWidth)

def qualifiedScalarWidthBits (profile : ScalarProfile)
    (type : CppQualifiedScalar) : Except ScalarWidthError Nat :=
  scalarWidthBits profile type.base

end LeanModels.Cpp
