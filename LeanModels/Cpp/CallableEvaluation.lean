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
  | missingReturn
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

private def unaryOperator? (operator : String) : Option IntegralUnary :=
  match operator with
  | "+" => some .plus
  | "-" => some .negate
  | "~" => some .complement
  | "!" => some .logicalNot
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
      | .convert operand => do
          let operandResult ← evaluateTyped fuel profile parameters arguments operand
          match operandResult with
          | .ok operandValue => convertTo profile typed.type operandValue
          | .invalid reason => pure (.invalid reason)
          | .undefined reason => pure (.undefined reason)
          | .unsupported reason => pure (.unsupported reason)
      | .unary operator operand => do
          let some operation := unaryOperator? operator
            | .error (.unsupportedOperator operator)
          let operandResult ← evaluateTyped fuel profile parameters arguments operand
          match operandResult with
          | .ok operandValue =>
              let result := integralUnary operation operandValue
              match result with
              | .ok value =>
                  let expected ← formatFor profile typed.type
                  if value.format == expected then pure result
                  else .error .expressionTypeMismatch
              | .invalid reason => pure (.invalid reason)
              | .undefined reason => pure (.undefined reason)
              | .unsupported reason => pure (.unsupported reason)
          | .invalid reason => pure (.invalid reason)
          | .undefined reason => pure (.undefined reason)
          | .unsupported reason => pure (.unsupported reason)
      | .logical operator left right => do
          unless operator == "&&" || operator == "||" do
            throw (.unsupportedOperator operator)
          let leftResult ← evaluateTyped fuel profile parameters arguments left
          match leftResult with
          | .ok leftValue =>
              let leftTrue := leftValue.value != 0
              if operator == "&&" && !leftTrue then
                pure (.ok (integralBoolean false))
              else if operator == "||" && leftTrue then
                pure (.ok (integralBoolean true))
              else
                let rightResult ← evaluateTyped fuel profile parameters arguments right
                match rightResult with
                | .ok rightValue => pure (.ok (integralBoolean (rightValue.value != 0)))
                | .invalid reason => pure (.invalid reason)
                | .undefined reason => pure (.undefined reason)
                | .unsupported reason => pure (.unsupported reason)
          | .invalid reason => pure (.invalid reason)
          | .undefined reason => pure (.undefined reason)
          | .unsupported reason => pure (.unsupported reason)
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

private inductive CallableExecution where
  | normal
  | returned (result : IntegralResult IntegralValue)
  | failed (result : IntegralResult IntegralValue)

private def terminalResult : IntegralResult IntegralValue → CallableExecution
  | .ok _ => .normal
  | result => .failed result

private def evaluateCallableStatement (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments : List IntegralValue)
    (statement : CallableStatement) :
    Except CallableEvaluationError CallableExecution :=
  match fuel with
  | 0 => .error .fuelExhausted
  | fuel + 1 =>
      match statement with
      | .skip => .ok .normal
      | .expression expression =>
          (evaluateTyped fuel profile parameters arguments expression).map terminalResult
      | .return_ expression =>
          (evaluateTyped fuel profile parameters arguments expression).map .returned
      | .conditional condition whenTrue whenFalse => do
          let result ← evaluateTyped fuel profile parameters arguments condition
          match result with
          | .ok value =>
              if value.value == 0 then
                evaluateCallableStatement fuel profile parameters arguments whenFalse
              else
                evaluateCallableStatement fuel profile parameters arguments whenTrue
          | .invalid reason => pure (.failed (.invalid reason))
          | .undefined reason => pure (.failed (.undefined reason))
          | .unsupported reason => pure (.failed (.unsupported reason))
      | .whileLoop condition body => do
          let result ← evaluateTyped fuel profile parameters arguments condition
          match result with
          | .ok value =>
              if value.value == 0 then
                pure .normal
              else
                let bodyResult ← evaluateCallableStatement fuel profile parameters arguments body
                match bodyResult with
                | .normal =>
                    evaluateCallableStatement fuel profile parameters arguments
                      (.whileLoop condition body)
                | .returned _ | .failed _ => pure bodyResult
          | .invalid reason => pure (.failed (.invalid reason))
          | .undefined reason => pure (.failed (.undefined reason))
          | .unsupported reason => pure (.failed (.unsupported reason))
      | .doWhile body condition => do
          let bodyResult ← evaluateCallableStatement fuel profile parameters arguments body
          match bodyResult with
          | .normal =>
              let result ← evaluateTyped fuel profile parameters arguments condition
              match result with
              | .ok value =>
                  if value.value == 0 then
                    pure .normal
                  else
                    evaluateCallableStatement fuel profile parameters arguments
                      (.doWhile body condition)
              | .invalid reason => pure (.failed (.invalid reason))
              | .undefined reason => pure (.failed (.undefined reason))
              | .unsupported reason => pure (.failed (.unsupported reason))
          | .returned _ | .failed _ => pure bodyResult
      | .sequence first second => do
          let firstResult ← evaluateCallableStatement fuel profile parameters arguments first
          match firstResult with
          | .normal => evaluateCallableStatement fuel profile parameters arguments second
          | .returned _ | .failed _ => pure firstResult

def evaluateCallable (fuel : Nat) (profile : TargetProfile) (function : CallableFunction)
    (arguments : List IntegralValue) :
    Except CallableEvaluationError (IntegralResult IntegralValue) := do
  unless profile.valid do throw .invalidProfile
  if arguments.length != function.parameters.length then
    throw .arityMismatch
  if fuel == 0 then throw .fuelExhausted
  let converted ← convertArguments profile function.parameters arguments
  match converted with
  | .ok values =>
      let execution ← evaluateCallableStatement fuel profile function.parameters values function.body
      match execution with
      | .normal => .error .missingReturn
      | .returned result | .failed result => .ok result
  | .invalid reason => pure (.invalid reason)
  | .undefined reason => pure (.undefined reason)
  | .unsupported reason => pure (.unsupported reason)

end LeanModels.Cpp
