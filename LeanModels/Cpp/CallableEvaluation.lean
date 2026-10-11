import LeanModels.Cpp.Callable

namespace LeanModels.Cpp

inductive CallableEvaluationError where
  | invalidProfile
  | arityMismatch
  | unsupportedType (type : CppTypeEvidence)
  | missingParameter (declaration : FrontendHandle)
  | argumentTypeMismatch (declaration : FrontendHandle)
  | unsupportedOperator (operator : String)
  | expressionTypeMismatch
  | resultTypeMismatch
  | fuelExhausted
  deriving Repr, BEq, Inhabited

private def builtinIntegralType : CppTypeEvidence → Option CppIntType
  | .builtin type => some type
  | .qualified _ _ base => builtinIntegralType base
  | _ => none

private def mapFormatError (reason : TypeResolutionError) : CallableEvaluationError :=
  match reason with
  | .invalidProfile => .invalidProfile
  | .unsupportedType type => .unsupportedType (.builtin type)

private def formatFor (profile : TargetProfile) (type : CppTypeEvidence) :
    Except CallableEvaluationError IntegralFormat :=
  match builtinIntegralType type with
  | none => .error (.unsupportedType type)
  | some integer =>
      match profile.format integer with
      | .ok format => .ok format
      | .error reason => .error (mapFormatError reason)

private def exactArgument (profile : TargetProfile) (type : CppTypeEvidence)
    (value : IntegralValue) (declaration : FrontendHandle) :
    Except CallableEvaluationError (IntegralResult IntegralValue) := do
  let expected ← formatFor profile type
  match value.invalid? with
  | some reason => pure (.invalid reason)
  | none =>
      if value.format == expected then
        pure (.ok value)
      else
        .error (.argumentTypeMismatch declaration)

private def convertTo (profile : TargetProfile) (type : CppTypeEvidence)
    (value : IntegralValue) : Except CallableEvaluationError (IntegralResult IntegralValue) := do
  let destination ← formatFor profile type
  pure (integralConvert destination value)

private def convertArguments (profile : TargetProfile) (parameters : List CallableParameter)
    (arguments : List IntegralValue) :
    Except CallableEvaluationError (IntegralResult (List IntegralValue)) :=
  match parameters, arguments with
  | [], [] => .ok (.ok [])
  | parameter :: remainingParameters, argument :: remainingArguments => do
      let converted ← convertTo profile parameter.type argument
      match converted with
      | .ok value =>
          let remaining ← convertArguments profile remainingParameters remainingArguments
          pure (match remaining with
            | .ok values => .ok (value :: values)
            | .invalid reason => .invalid reason
            | .undefined reason => .undefined reason
            | .unsupported reason => .unsupported reason)
      | .invalid reason => pure (.invalid reason)
      | .undefined reason => pure (.undefined reason)
      | .unsupported reason => pure (.unsupported reason)
  | _, _ => .error .arityMismatch

private def operator? (operator : String) : Option IntegralBinary :=
  match operator with
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

private def argumentAt (arguments : List IntegralValue) (index : Nat) : Option IntegralValue :=
  arguments[index]?

private def evaluateInteger (profile : TargetProfile) (value : Nat) :
    Except CallableEvaluationError (IntegralResult IntegralValue) := do
  let format ← formatFor profile (.builtin .int)
  let literal : IntegralValue := {format, value := Int.ofNat value}
  pure (match literal.invalid? with
    | some reason => .invalid reason
    | none => .ok literal)

private def evaluateParameter (profile : TargetProfile) (parameters : List CallableParameter)
    (arguments : List IntegralValue) (typed : TypedCallableExpression)
    (declaration : FrontendHandle) :
    Except CallableEvaluationError (IntegralResult IntegralValue) := do
  let some index := parameters.findIdx? (fun parameter => parameter.declaration == declaration)
    | .error (.missingParameter declaration)
  let some parameter := parameters[index]?
    | .error (.missingParameter declaration)
  let some argument := argumentAt arguments index
    | .error .arityMismatch
  let exact ← exactArgument profile parameter.type argument declaration
  match exact with
  | .ok value => convertTo profile typed.type value
  | .invalid reason => pure (.invalid reason)
  | .undefined reason => pure (.undefined reason)
  | .unsupported reason => pure (.unsupported reason)

private def evaluateTyped (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments : List IntegralValue)
    (typed : TypedCallableExpression) :
    Except CallableEvaluationError (IntegralResult IntegralValue) :=
  match fuel with
  | 0 => .error .fuelExhausted
  | fuel + 1 =>
      match typed.expression with
      | .integer value => evaluateInteger profile value
      | .parameter declaration => evaluateParameter profile parameters arguments typed declaration
      | .binary operator left right => do
          let some operation := operator? operator
            | .error (.unsupportedOperator operator)
          let leftResult ← evaluateTyped fuel profile parameters arguments left
          let rightResult ← evaluateTyped fuel profile parameters arguments right
          match leftResult, rightResult with
          | .ok leftValue, .ok rightValue =>
              let result := integralBinary operation leftValue rightValue
              match result with
              | .ok value =>
                  let expected ← formatFor profile typed.type
                  if value.format == expected then pure result
                  else .error .expressionTypeMismatch
              | .invalid reason => pure (.invalid reason)
              | .undefined reason => pure (.undefined reason)
              | .unsupported reason => pure (.unsupported reason)
          | .invalid reason, _ | _, .invalid reason => pure (.invalid reason)
          | .undefined reason, _ | _, .undefined reason => pure (.undefined reason)
          | .unsupported reason, _ | _, .unsupported reason => pure (.unsupported reason)

def evaluateCallable (fuel : Nat) (profile : TargetProfile) (function : CallableFunction)
    (arguments : List IntegralValue) :
    Except CallableEvaluationError (IntegralResult IntegralValue) := do
  unless profile.valid do throw .invalidProfile
  if arguments.length != function.parameters.length then
    throw .arityMismatch
  unless function.signature.result == function.body.type do
    throw .resultTypeMismatch
  if fuel == 0 then throw .fuelExhausted
  let converted ← convertArguments profile function.parameters arguments
  match converted with
  | .ok values => evaluateTyped fuel profile function.parameters values function.body
  | .invalid reason => pure (.invalid reason)
  | .undefined reason => pure (.undefined reason)
  | .unsupported reason => pure (.unsupported reason)

end LeanModels.Cpp
