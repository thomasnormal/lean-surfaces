import LeanModels.Cpp.IntegralObjectExpressions

namespace LeanModels.Cpp

inductive IntegralObjectStatement where
  | expression (expression : IntegralObjectExpression)
  | assign (access : IntegralObjectRef) (sourceType : CppTypeEvidence)
      (expression : IntegralObjectExpression)
  | sequence (first second : IntegralObjectStatement)
  deriving Repr, BEq, Inhabited

inductive IntegralObjectStatementError where
  | fuelExhausted
  | object (reason : IntegralObjectError)
  | invalid (reason : InvalidIntegral)
  | undefined (reason : IntegralUB)
  | unsupported (reason : IntegralUnsupported)
  deriving Repr, BEq, Inhabited

private def mapExpressionError : IntegralObjectExpressionError → IntegralObjectStatementError
  | .fuelExhausted => .fuelExhausted
  | .object reason => .object reason

private def mapResult : IntegralResult IntegralValue →
    Except IntegralObjectStatementError (Option IntegralValue)
  | .ok value => .ok (some value)
  | .invalid reason => .error (.invalid reason)
  | .undefined reason => .error (.undefined reason)
  | .unsupported reason => .error (.unsupported reason)

private def executeStep (fuel : Nat) (store : IntegralObjectStore)
    (statement : IntegralObjectStatement) :
    Except IntegralObjectStatementError IntegralObjectStore :=
  match fuel with
  | 0 => .error .fuelExhausted
  | fuel + 1 =>
      match statement with
      | .expression expression => do
          let result ← (evaluateIntegralObjectExpression fuel store expression).mapError
            mapExpressionError
          let _ ← mapResult result
          pure store
      | .assign access sourceType expression => do
          let result ← (evaluateIntegralObjectExpression fuel store expression).mapError
            mapExpressionError
          match result with
          | .ok value => (store.assignConverted access sourceType value).mapError (.object)
          | .invalid reason => throw (.invalid reason)
          | .undefined reason => throw (.undefined reason)
          | .unsupported reason => throw (.unsupported reason)
      | .sequence first second => do
          let store ← executeStep fuel store first
          executeStep fuel store second

def executeIntegralObjectStatement (fuel : Nat) (store : IntegralObjectStore)
    (statement : IntegralObjectStatement) :
    Except IntegralObjectStatementError IntegralObjectStore :=
  executeStep fuel store statement

end LeanModels.Cpp
