import LeanModels.Cpp.IntegralObjects

namespace LeanModels.Cpp

inductive IntegralObjectExpression where
  | literal (value : IntegralValue)
  | read (access : IntegralObjectRef)
  | unary (operation : IntegralUnary) (operand : IntegralObjectExpression)
  | binary (operation : IntegralBinary)
      (left right : IntegralObjectExpression)
  deriving Repr, BEq, Inhabited

inductive IntegralObjectExpressionError where
  | fuelExhausted
  | object (reason : IntegralObjectError)
  deriving Repr, BEq, Inhabited

private def propagate : IntegralResult IntegralValue →
    IntegralResult IntegralValue → IntegralResult IntegralValue → IntegralResult IntegralValue
  | .ok _, .invalid reason, _ | .invalid reason, _, _ => .invalid reason
  | .ok _, .undefined reason, _ | .undefined reason, _, _ => .undefined reason
  | .ok _, .unsupported reason, _ | .unsupported reason, _, _ => .unsupported reason
  | .ok _, .ok _, result => result

private def evaluateStep (fuel : Nat) (store : IntegralObjectStore)
    (expression : IntegralObjectExpression) :
    Except IntegralObjectExpressionError (IntegralResult IntegralValue) :=
  match fuel with
  | 0 => .error .fuelExhausted
  | fuel + 1 =>
      match expression with
      | .literal value =>
          match value.invalid? with
          | some reason => .ok (.invalid reason)
          | none => .ok (.ok value)
      | .read access =>
          (store.read access).mapError (.object)
            |>.map IntegralResult.ok
      | .unary operation operand => do
          let result ← evaluateStep fuel store operand
          pure (match result with
            | .ok value => integralUnary operation value
            | .invalid reason => .invalid reason
            | .undefined reason => .undefined reason
            | .unsupported reason => .unsupported reason)
      | .binary operation left right => do
          let leftResult ← evaluateStep fuel store left
          let rightResult ← evaluateStep fuel store right
          match leftResult, rightResult with
          | .ok leftValue, .ok rightValue =>
              pure (integralBinary operation leftValue rightValue)
          | leftValue, rightValue =>
              pure (propagate leftValue rightValue (.invalid .zeroWidth))

def evaluateIntegralObjectExpression (fuel : Nat) (store : IntegralObjectStore)
    (expression : IntegralObjectExpression) :
    Except IntegralObjectExpressionError (IntegralResult IntegralValue) :=
  evaluateStep fuel store expression

def assignIntegralObjectExpression (fuel : Nat) (store : IntegralObjectStore)
    (access : IntegralObjectRef) (sourceType : CppTypeEvidence)
    (expression : IntegralObjectExpression) :
    Except IntegralObjectExpressionError IntegralObjectStore := do
  let result ← evaluateIntegralObjectExpression fuel store expression
  match result with
  | .ok value => (store.assignConverted access sourceType value).mapError (.object)
  | .invalid reason => throw (.object (.invalidValue reason))
  | .undefined _ => throw (.object (.invalidValue .outOfRange))
  | .unsupported _ => throw (.object .valueTypeMismatch)

end LeanModels.Cpp
