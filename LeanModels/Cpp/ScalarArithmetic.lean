import LeanModels.Cpp.Types
import LeanModels.Cpp.Integral

namespace LeanModels.Cpp

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

end LeanModels.Cpp
