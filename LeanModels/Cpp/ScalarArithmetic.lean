import LeanModels.Cpp.Types
import LeanModels.Cpp.Integral
import LeanModels.Cpp.TypeEvidence

namespace LeanModels.Cpp

def integralTypeOfEvidence : CppTypeEvidence → Option CppIntType
  | .builtin type => some type
  | .qualified _ _ base => integralTypeOfEvidence base
  | _ => none

def integralFormatOfEvidence (profile : TargetProfile) (type : CppTypeEvidence) :
    Except TypeResolutionError IntegralFormat := do
  let some integer := integralTypeOfEvidence type
    | throw (.unsupportedType .int)
  profile.format integer

def integralBinaryOfString : String → Option IntegralBinary
  | "+" => some .add
  | "-" => some .subtract
  | "*" => some .multiply
  | "/" => some .divide
  | "%" => some .remainder
  | "<<" => some .shiftLeft
  | ">>" => some .shiftRight
  | "&" => some .bitAnd
  | "|" => some .bitOr
  | "^" => some .bitXor
  | "==" => some .equal
  | "!=" => some .notEqual
  | "<" => some .less
  | "<=" => some .lessEqual
  | ">" => some .greater
  | ">=" => some .greaterEqual
  | _ => none

def integralUnaryOfString : String → Option IntegralUnary
  | "+" => some .plus
  | "-" => some .negate
  | "~" => some .complement
  | "!" => some .logicalNot
  | _ => none

private def mapIntegralResult (result : IntegralResult IntegralValue)
    (continuation : IntegralValue → IntegralResult IntegralValue) :
    IntegralResult IntegralValue :=
  match result with
  | .ok value => continuation value
  | .invalid reason => .invalid reason
  | .undefined reason => .undefined reason
  | .unsupported reason => .unsupported reason

/-- Execute an integral binary operation after C++'s promotions and usual
arithmetic conversions select one common destination format. The conversion
boundary is explicit so mixed signed/unsigned operands cannot silently reach
the same-format kernel with the wrong representation. -/
def integralBinaryUsual (profile : TargetProfile) (operation : IntegralBinary)
    (leftType rightType : CppIntType) (left right : IntegralValue) :
    IntegralResult IntegralValue :=
  if operation == .shiftLeft || operation == .shiftRight then
    match integralPromotion profile leftType, integralPromotion profile rightType with
    | .ok leftPromoted, .ok rightPromoted =>
        match profile.format leftPromoted, profile.format rightPromoted with
        | .ok leftFormat, .ok rightFormat =>
            mapIntegralResult (integralConvert leftFormat left) fun left =>
              mapIntegralResult (integralConvert rightFormat right) fun right =>
                integralBinary operation left right
        | _, _ => .unsupported .unresolvedArithmeticConversions
    | _, _ => .unsupported .unresolvedArithmeticConversions
  else
    match resolveArithmeticFormats profile leftType rightType with
    | .error _ => .unsupported .unresolvedArithmeticConversions
    | .ok (_, format) =>
        mapIntegralResult (integralConvert format left) fun left =>
          mapIntegralResult (integralConvert format right) fun right =>
            integralBinary operation left right

def integralSizeBytes (profile : TargetProfile) (type : CppIntType) :
    Except TypeResolutionError Nat :=
  match profile.format type with
  | .ok format => .ok ((format.width + 7) / 8)
  | .error reason => .error reason

def integralAlignBytes (profile : TargetProfile) (type : CppIntType) :
    Except TypeResolutionError Nat :=
  match integralSizeBytes profile type with
  | .ok bytes => .ok bytes
  | .error reason => .error reason

end LeanModels.Cpp
