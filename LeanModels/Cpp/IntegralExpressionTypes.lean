import LeanModels.Cpp.ReferenceTypes

namespace LeanModels.Cpp

inductive CppIntegralUnaryOperator where
  | plus
  | minus
  | bitNot
  | logicalNot
  deriving Repr, BEq, Inhabited

inductive CppIntegralBinaryOperator where
  | add
  | subtract
  | multiply
  | divide
  | remainder
  | shiftLeft
  | shiftRight
  | bitAnd
  | bitOr
  | bitXor
  | equal
  | notEqual
  | less
  | lessEqual
  | greater
  | greaterEqual
  deriving Repr, BEq, Inhabited

namespace CppIntegralBinaryOperator

def isShift : CppIntegralBinaryOperator → Bool
  | .shiftLeft | .shiftRight => true
  | _ => false

def isComparison : CppIntegralBinaryOperator → Bool
  | .equal | .notEqual | .less | .lessEqual | .greater | .greaterEqual => true
  | _ => false

end CppIntegralBinaryOperator

inductive IntegralExpressionTypeError where
  | invalidProfile
  | unsupportedType (type : CppIntType)
  deriving Repr, BEq, Inhabited

private def mapTypeError : TypeResolutionError → IntegralExpressionTypeError
  | .invalidProfile => .invalidProfile
  | .unsupportedType type => .unsupportedType type

private def mapTypeResult (result : Except TypeResolutionError CppIntType) :
    Except IntegralExpressionTypeError CppIntType :=
  match result with
  | .ok type => .ok type
  | .error reason => .error (mapTypeError reason)

def integralUnaryType (profile : TargetProfile)
    (operator : CppIntegralUnaryOperator) (operand : CppIntType) :
    Except IntegralExpressionTypeError CppIntType :=
  match operator with
  | .logicalNot =>
      match profile.format operand with
      | .ok _ => .ok .boolean
      | .error reason => .error (mapTypeError reason)
  | .plus | .minus | .bitNot => mapTypeResult (integralPromotion profile operand)

def integralBinaryType (profile : TargetProfile)
    (operator : CppIntegralBinaryOperator) (left right : CppIntType) :
    Except IntegralExpressionTypeError CppIntType :=
  if operator.isShift then
    match integralPromotion profile left, integralPromotion profile right with
    | .ok promotedLeft, .ok _ => .ok promotedLeft
    | .error reason, _ => .error (mapTypeError reason)
    | _, .error reason => .error (mapTypeError reason)
  else
    let result := usualArithmeticType profile left right
    match result with
    | .ok common => .ok (if operator.isComparison then .boolean else common)
    | .error reason => .error (mapTypeError reason)

structure CppTypedExpression where
  type : CppType
  category : CppValueCategory
  deriving Repr, BEq, Inhabited

def typedIntegralResult (type : CppIntType) : CppTypedExpression :=
  {type := .scalar (.integral type), category := .prvalue}

def inferIntegralUnary (profile : TargetProfile)
    (operator : CppIntegralUnaryOperator) (operand : CppIntType) :
    Except IntegralExpressionTypeError CppTypedExpression :=
  (integralUnaryType profile operator operand).map typedIntegralResult

def inferIntegralBinary (profile : TargetProfile)
    (operator : CppIntegralBinaryOperator) (left right : CppIntType) :
    Except IntegralExpressionTypeError CppTypedExpression :=
  (integralBinaryType profile operator left right).map typedIntegralResult

end LeanModels.Cpp
