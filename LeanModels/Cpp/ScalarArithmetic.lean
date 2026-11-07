import LeanModels.Cpp.Types
import LeanModels.Cpp.Integral

namespace LeanModels.Cpp

inductive IntegralLogical where
  | conjunction
  | disjunction
  deriving Repr, BEq

def integralLogicalOfString : String → Option IntegralLogical
  | "&&" => some .conjunction
  | "||" => some .disjunction
  | _ => none

/-- The short-circuit result for a logical operation, when its left operand
    decides the result. A missing result means that the right operand must be
    evaluated. -/
def integralLogicalShortCircuit (operation : IntegralLogical) (left : IntegralValue) :
    Option IntegralValue :=
  match operation with
  | .conjunction => if left.value == 0 then some (integralBoolean false) else none
  | .disjunction => if left.value == 0 then none else some (integralBoolean true)

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
