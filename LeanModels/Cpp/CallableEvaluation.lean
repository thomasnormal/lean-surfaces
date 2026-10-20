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
  | breakOutsideLoop
  | continueOutsideLoop
  | unsupportedDeclaration
  | unsequencedEffects
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

private def assignParameter (profile : TargetProfile) (parameters : List CallableParameter)
    (arguments : List IntegralValue) (declaration : FrontendHandle) (value : IntegralValue) :
    Except CallableEvaluationError (List IntegralValue) := do
  let some index := parameters.findIdx? (fun parameter => parameter.declaration == declaration)
    | .error (.missingParameter declaration)
  let some parameter := parameters[index]?
    | .error (.missingParameter declaration)
  let expected ← formatFor profile parameter.type
  unless value.format == expected do
    throw .expressionTypeMismatch
  pure (arguments.set index value)

private def parameterValue (parameters : List CallableParameter)
    (arguments : List IntegralValue) (declaration : FrontendHandle) :
    Except CallableEvaluationError IntegralValue := do
  let some index := parameters.findIdx? (fun parameter => parameter.declaration == declaration)
    | .error (.missingParameter declaration)
  let some value := arguments[index]?
    | .error (.missingParameter declaration)
  pure value

private def evaluateIncrement (profile : TargetProfile) (parameters : List CallableParameter)
    (arguments : List IntegralValue) (operator : String) (isPostfix : Bool)
    (declaration : FrontendHandle) :
    Except CallableEvaluationError (IntegralResult IntegralValue × List IntegralValue) := do
  let some parameter := parameters.find? (fun parameter => parameter.declaration == declaration)
    | throw (.missingParameter declaration)
  let .builtin type := parameter.type
    | throw (.unsupportedType parameter.type)
  if type == .boolean then throw (.unsupportedType parameter.type)
  let operation ← match operator with
    | "++" => pure IntegralBinary.add
    | "--" => pure IntegralBinary.subtract
    | _ => throw (.unsupportedOperator operator)
  let common ← match usualArithmeticType profile type .int with
    | .ok type => pure type
    | .error reason => throw (mapFormatError reason)
  let current ← parameterValue parameters arguments declaration
  let converted ← convertTo profile (.builtin common) current
  match converted with
  | .ok operand =>
      match integralBinary operation operand ⟨operand.format, 1⟩ with
      | .ok result =>
          let stored ← convertTo profile parameter.type result
          match stored with
          | .ok value =>
              let updated ← assignParameter profile parameters arguments declaration value
              pure (.ok (if isPostfix then current else value), updated)
          | result => pure (result, arguments)
      | result => pure (result, arguments)
  | result => pure (result, arguments)

private def evaluateInteger (profile : TargetProfile) (typed : TypedCallableExpression) (value : Nat) :
    Except CallableEvaluationError (IntegralResult IntegralValue) := do
  let format ← formatFor profile typed.sourceType
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
    Except CallableEvaluationError (IntegralResult IntegralValue × List IntegralValue) :=
  match fuel with
  | 0 => .error .fuelExhausted
  | fuel + 1 =>
      match typed.expression with
      | .integer value => (evaluateInteger profile typed value).map (fun result => (result, arguments))
      | .parameter declaration =>
          (evaluateParameter profile parameters arguments typed declaration).map
            (fun result => (result, arguments))
      | .increment operator isPostfix declaration => do
          let (result, updated) ← evaluateIncrement profile parameters arguments operator isPostfix declaration
          match result with
          | .ok value =>
              let expected ← formatFor profile typed.type
              unless value.format == expected do throw .expressionTypeMismatch
              pure (result, updated)
          | _ => pure (result, updated)
      | .convert operand => do
          let (operandResult, updated) ← evaluateTyped fuel profile parameters arguments operand
          match operandResult with
          | .ok operandValue =>
              (convertTo profile typed.type operandValue).map (fun result => (result, updated))
          | result => pure (result, updated)
      | .unary operator operand => do
          let some operation := unaryOperator? operator
            | .error (.unsupportedOperator operator)
          let (operandResult, updated) ← evaluateTyped fuel profile parameters arguments operand
          match operandResult with
          | .ok operandValue =>
              let result := integralUnary operation operandValue
              match result with
              | .ok value =>
                  let expected ← formatFor profile typed.type
                  if value.format == expected then pure (result, updated)
                  else .error .expressionTypeMismatch
              | result => pure (result, updated)
          | result => pure (result, updated)
      | .conditional condition whenTrue whenFalse => do
          let (conditionResult, afterCondition) ←
            evaluateTyped fuel profile parameters arguments condition
          match conditionResult with
          | .ok value =>
              if value.value == 0 then
                evaluateTyped fuel profile parameters afterCondition whenFalse
              else
                evaluateTyped fuel profile parameters afterCondition whenTrue
          | result => pure (result, afterCondition)
      | .comma left right => do
          let (leftResult, afterLeft) ← evaluateTyped fuel profile parameters arguments left
          match leftResult with
          | .ok _ => evaluateTyped fuel profile parameters afterLeft right
          | result => pure (result, afterLeft)
      | .logical operator left right => do
          unless operator == "&&" || operator == "||" do
            throw (.unsupportedOperator operator)
          let (leftResult, afterLeft) ← evaluateTyped fuel profile parameters arguments left
          match leftResult with
          | .ok leftValue =>
              let leftTrue := leftValue.value != 0
              if operator == "&&" && !leftTrue then
                pure (.ok (integralBoolean false), afterLeft)
              else if operator == "||" && leftTrue then
                pure (.ok (integralBoolean true), afterLeft)
              else
                let (rightResult, afterRight) ← evaluateTyped fuel profile parameters afterLeft right
                match rightResult with
                | .ok rightValue => pure (.ok (integralBoolean (rightValue.value != 0)), afterRight)
                | result => pure (result, afterRight)
          | result => pure (result, afterLeft)
      | .binary operator left right => do
          if left.expression.hasEffects || right.expression.hasEffects then
            throw .unsequencedEffects
          let some operation := operator? operator
            | .error (.unsupportedOperator operator)
          let (leftResult, _) ← evaluateTyped fuel profile parameters arguments left
          let (rightResult, _) ← evaluateTyped fuel profile parameters arguments right
          match leftResult, rightResult with
          | .ok leftValue, .ok rightValue =>
              let result := integralBinary operation leftValue rightValue
              match result with
              | .ok value =>
                  let expected ← formatFor profile typed.type
                  if value.format == expected then pure (result, arguments)
                  else .error .expressionTypeMismatch
              | result => pure (result, arguments)
          | .invalid reason, _ | _, .invalid reason => pure (.invalid reason, arguments)
          | .undefined reason, _ | _, .undefined reason => pure (.undefined reason, arguments)
          | .unsupported reason, _ | _, .unsupported reason => pure (.unsupported reason, arguments)

private inductive CallableExecution where
  | normal (arguments : List IntegralValue)
  | returned (result : IntegralResult IntegralValue) (arguments : List IntegralValue)
  | failed (result : IntegralResult IntegralValue) (arguments : List IntegralValue)
  | break_ (arguments : List IntegralValue)
  | continue_ (arguments : List IntegralValue)

private def terminalResult (arguments : List IntegralValue) :
    IntegralResult IntegralValue → CallableExecution
  | .ok _ => .normal arguments
  | result => .failed result arguments

private def switchCaseSuffix (value : Int) : List CallableSwitchClause → Option (List CallableSwitchClause)
  | [] => none
  | clause :: rest =>
      match clause.label with
      | some label => if label == value then some (clause :: rest) else switchCaseSuffix value rest
      | none => switchCaseSuffix value rest

private def switchDefaultSuffix : List CallableSwitchClause → Option (List CallableSwitchClause)
  | [] => none
  | clause :: rest =>
      match clause.label with
      | some _ => switchDefaultSuffix rest
      | none => some (clause :: rest)

mutual
  /-- Iterations exclude the initializer, which the for statement executes once.
  Body completion (including continue through a switch) reaches the step only
  after the body has returned. Inner loops consume their own transfers. -/
  private partial def evaluateForIterations (fuel : Nat) (profile : TargetProfile)
      (parameters : List CallableParameter) (arguments : List IntegralValue)
      (condition : TypedCallableExpression) (step body : CallableStatement) :
      Except CallableEvaluationError CallableExecution := do
    match fuel with
    | 0 => throw .fuelExhausted
    | fuel + 1 =>
        let (result, afterCondition) ← evaluateTyped fuel profile parameters arguments condition
        match result with
        | .ok value =>
            if value.value == 0 then
              pure (.normal afterCondition)
            else
              let bodyResult ← evaluateCallableStatement fuel profile parameters afterCondition body
              match bodyResult with
              | .normal updated | .continue_ updated =>
                  let stepResult ← evaluateCallableStatement fuel profile parameters updated step
                  match stepResult with
                  | .normal afterStep =>
                      evaluateForIterations fuel profile parameters afterStep condition step body
                  | _ => pure stepResult
              | .break_ updated => pure (.normal updated)
              | .returned _ _ | .failed _ _ => pure bodyResult
        | result => pure (.failed result afterCondition)

  private partial def evaluateSwitchClauses (fuel : Nat) (profile : TargetProfile)
      (parameters : List CallableParameter) (arguments : List IntegralValue)
      : List CallableSwitchClause → Except CallableEvaluationError CallableExecution
    | [] => .ok (.normal arguments)
    | clause :: rest => do
        let result ← evaluateCallableStatement fuel profile parameters arguments clause.body
        match result with
        | .normal updated => evaluateSwitchClauses fuel profile parameters updated rest
        | .break_ updated => pure (.normal updated)
        | .returned _ _ | .failed _ _ | .continue_ _ => pure result

  private partial def evaluateCallableStatement (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments : List IntegralValue)
    (statement : CallableStatement) :
    Except CallableEvaluationError CallableExecution :=
  match fuel with
  | 0 => .error .fuelExhausted
  | fuel + 1 =>
      match statement with
      | .skip => .ok (.normal arguments)
      | .automatic _ => throw .unsupportedDeclaration
      | .block body => evaluateCallableStatement fuel profile parameters arguments body
      | .expression expression =>
          (evaluateTyped fuel profile parameters arguments expression).map
            (fun (result, updated) => terminalResult updated result)
      | .assign declaration expression => do
          let (result, afterExpression) ← evaluateTyped fuel profile parameters arguments expression
          match result with
          | .ok value =>
              match assignParameter profile parameters afterExpression declaration value with
              | .ok updated => pure (.normal updated)
              | .error error => throw error
          | result => pure (.failed result afterExpression)
      | .compoundAssign operator declaration expression => do
          let some arithmeticOperator := compoundAssignmentOperator? operator
            | throw (.unsupportedOperator operator)
          let some operation := operator? arithmeticOperator
            | throw (.unsupportedOperator operator)
          let (result, afterExpression) ← evaluateTyped fuel profile parameters arguments expression
          match result with
          | .ok rightValue =>
              let current ← parameterValue parameters afterExpression declaration
              match integralBinary operation current rightValue with
              | .ok value =>
                  match assignParameter profile parameters afterExpression declaration value with
                  | .ok updated => pure (.normal updated)
                  | .error error => throw error
              | result => pure (.failed result afterExpression)
          | result => pure (.failed result afterExpression)
      | .return_ expression =>
          (evaluateTyped fuel profile parameters arguments expression).map
            (fun (result, updated) => .returned result updated)
      | .conditional condition whenTrue whenFalse => do
          let (result, afterCondition) ← evaluateTyped fuel profile parameters arguments condition
          match result with
          | .ok value =>
              if value.value == 0 then
                evaluateCallableStatement fuel profile parameters afterCondition whenFalse
              else
                evaluateCallableStatement fuel profile parameters afterCondition whenTrue
          | result => pure (.failed result afterCondition)
      | .switch_ condition clauses => do
          let (result, afterCondition) ← evaluateTyped fuel profile parameters arguments condition
          match result with
          | .ok value =>
              let selected := (switchCaseSuffix value.value clauses).orElse
                (fun _ => switchDefaultSuffix clauses) |>.getD []
              evaluateSwitchClauses fuel profile parameters afterCondition selected
          | result => pure (.failed result afterCondition)
      | .whileLoop condition body => do
          let (result, afterCondition) ← evaluateTyped fuel profile parameters arguments condition
          match result with
          | .ok value =>
              if value.value == 0 then
                pure (.normal afterCondition)
              else
                let bodyResult ← evaluateCallableStatement fuel profile parameters afterCondition body
                match bodyResult with
                | .normal updated =>
                    evaluateCallableStatement fuel profile parameters updated
                      (.whileLoop condition body)
                | .continue_ updated =>
                    evaluateCallableStatement fuel profile parameters updated
                      (.whileLoop condition body)
                | .break_ updated => pure (.normal updated)
                | .returned _ _ | .failed _ _ => pure bodyResult
          | result => pure (.failed result afterCondition)
      | .doWhile body condition => do
          let bodyResult ← evaluateCallableStatement fuel profile parameters arguments body
          match bodyResult with
          | .normal updated =>
              let (result, afterCondition) ← evaluateTyped fuel profile parameters updated condition
              match result with
              | .ok value =>
                  if value.value == 0 then
                    pure (.normal afterCondition)
                  else
                    evaluateCallableStatement fuel profile parameters afterCondition
                      (.doWhile body condition)
              | result => pure (.failed result afterCondition)
          | .continue_ updated =>
              let (result, afterCondition) ← evaluateTyped fuel profile parameters updated condition
              match result with
              | .ok value =>
                  if value.value == 0 then
                    pure (.normal afterCondition)
                  else
                    evaluateCallableStatement fuel profile parameters afterCondition
                      (.doWhile body condition)
              | result => pure (.failed result afterCondition)
          | .break_ updated => pure (.normal updated)
          | .returned _ _ | .failed _ _ => pure bodyResult
      | .forLoop initializer condition step body => do
          let initialResult ← evaluateCallableStatement fuel profile parameters arguments initializer
          match initialResult with
          | .normal updated => evaluateForIterations fuel profile parameters updated condition step body
          | _ => pure initialResult
      | .break_ => pure (.break_ arguments)
      | .continue_ => pure (.continue_ arguments)
      | .sequence first second => do
          let firstResult ← evaluateCallableStatement fuel profile parameters arguments first
          match firstResult with
          | .normal updated => evaluateCallableStatement fuel profile parameters updated second
          | .returned _ _ | .failed _ _ | .break_ _ | .continue_ _ => pure firstResult

end

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
      | .normal _ => .error .missingReturn
      | .returned result _ | .failed result _ => .ok result
      | .break_ _ => .error .breakOutsideLoop
      | .continue_ _ => .error .continueOutsideLoop
  | .invalid reason => pure (.invalid reason)
  | .undefined reason => pure (.undefined reason)
  | .unsupported reason => pure (.unsupported reason)

end LeanModels.Cpp
