import LeanModels.Cpp.CallableValueEvaluation
import LeanModels.Cpp.CallableObjectEvaluation

namespace LeanModels.Cpp

open CallableObjectEvaluation

/-- Project the authoritative frame evaluator through the historical value API.

The object evaluator is the one callable semantics.  This entry point keeps the
small value-facing result type used by callers, but does not interpret the
callable a second time.  Argument failures that are part of `IntegralResult`
remain values; frame/setup failures remain typed evaluator errors. -/
def evaluateCallable (fuel : Nat) (profile : TargetProfile)
    (function : CallableFunction) (arguments : List IntegralValue) :
    Except CallableEvaluationError (IntegralResult IntegralValue) :=
  match evaluateCallableObject fuel profile function arguments with
  | .ok result => .ok result
  | .error (.invalidProfile) => .error .invalidProfile
  | .error (.arityMismatch) => .error .arityMismatch
  | .error (.invalidArgument reason) => .ok (.invalid reason)
  | .error (.undefinedArgument reason) => .ok (.undefined reason)
  | .error (.unsupportedArgument reason) => .ok (.unsupported reason)
  | .error (.argumentTypeMismatch declaration) => .error (.argumentTypeMismatch declaration)
  | .error (.unsupportedOperator operator) => .error (.unsupportedOperator operator)
  | .error (.unsupportedCall) => .error .unsupportedCall
  | .error (.voidResultRequiresResultAPI) => .error (.unsupportedType .void)
  | .error (.returnTypeMismatch) => .error .resultTypeMismatch
  | .error (.missingReturn) => .error .missingReturn
  | .error (.breakOutsideLoop) => .error .breakOutsideLoop
  | .error (.continueOutsideLoop) => .error .continueOutsideLoop
  | .error (.gotoOutsideFunction label) => .error (.gotoOutsideFunction label)
  | .error (.frameError reason) => .error (.frameError reason)

/-- Successful integral values are observed through exactly the object-backed
callable run. Argument/setup refusals may use the value API's historical error
shape, but they cannot become a successful integral result. -/
theorem evaluateCallable_ok_value_iff (fuel : Nat) (profile : TargetProfile)
    (function : CallableFunction) (arguments : List IntegralValue) (value : IntegralValue) :
    evaluateCallable fuel profile function arguments = .ok (.ok value) ↔
      CallableObjectEvaluation.evaluateCallableObject fuel profile function arguments =
        .ok (.ok value) := by
  cases hresult : CallableObjectEvaluation.evaluateCallableObject fuel profile function arguments with
  | ok result => simp [evaluateCallable, hresult]
  | error reason => cases reason <;> simp [evaluateCallable, hresult]

/-- Direct calls have one public refusal cause in both callable APIs. -/
theorem evaluateCallable_unsupportedCall_iff (fuel : Nat) (profile : TargetProfile)
    (function : CallableFunction) (arguments : List IntegralValue) :
    evaluateCallable fuel profile function arguments = .error .unsupportedCall ↔
      CallableObjectEvaluation.evaluateCallableObject fuel profile function arguments =
        .error .unsupportedCall := by
  cases hresult : CallableObjectEvaluation.evaluateCallableObject fuel profile function arguments with
  | ok result => simp [evaluateCallable, hresult]
  | error reason => cases reason <;> simp [evaluateCallable, hresult]

end LeanModels.Cpp
