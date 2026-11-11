import LeanModels.Cpp.Callable
import LeanModels.Cpp.ScalarArithmetic

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
  | gotoOutsideFunction (label : String)
  | unsupportedDeclaration
  | unsequencedEffects
  | unsupportedCall
  | frameError (reason : FrameError)
  | fuelExhausted
  deriving Repr, BEq, Inhabited

private def mapFormatError (reason : TypeResolutionError) : CallableEvaluationError :=
  match reason with
  | .invalidProfile => .invalidProfile
  | .unsupportedType type => .unsupportedType (.builtin type)

private def formatFor (profile : TargetProfile) (type : CppTypeEvidence) :
    Except CallableEvaluationError IntegralFormat :=
  (integralFormatOfEvidence profile type).mapError mapFormatError

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
  (integralConvertOfEvidence profile type value).mapError mapFormatError

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
  let some operation := integralIncrementBinaryOfString operator
    | throw (.unsupportedOperator operator)
  let current ← parameterValue parameters arguments declaration
  match integralIncrementValue profile parameter.type operation current with
  | .ok value =>
      let updated ← assignParameter profile parameters arguments declaration value
      pure (.ok (if isPostfix then current else value), updated)
  | result => pure (result, arguments)

private def evaluateInteger (profile : TargetProfile) (typed : TypedCallableExpression) (value : Nat) :
    Except CallableEvaluationError (IntegralResult IntegralValue) := do
  let literal ← (integralLiteralOfEvidence profile typed.sourceType value).mapError mapFormatError
  pure (match literal.invalid? with
    | some reason => .invalid reason
    | none => .ok literal)

private def evaluateSizeOf (profile : TargetProfile) (typed : TypedCallableExpression)
    (operandType : CppTypeEvidence) :
    Except CallableEvaluationError (IntegralResult IntegralValue) := do
  (integralSizeValueOfEvidence profile typed.type operandType).map
    (fun value => .ok value)
    |>.mapError mapFormatError

private def evaluateAlignOf (profile : TargetProfile) (typed : TypedCallableExpression)
    (operandType : CppTypeEvidence) :
    Except CallableEvaluationError (IntegralResult IntegralValue) := do
  (integralAlignValueOfEvidence profile typed.type operandType).map
    (fun value => .ok value)
    |>.mapError mapFormatError

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

private inductive CallableExecution where
  | normal (arguments : List IntegralValue)
  | returned (result : IntegralResult IntegralValue) (arguments : List IntegralValue)
  | failed (result : IntegralResult IntegralValue) (arguments : List IntegralValue)
  | break_ (arguments : List IntegralValue)
  | continue_ (arguments : List IntegralValue)
  | goto_ (label : String) (arguments : List IntegralValue)

private def terminalResult (arguments : List IntegralValue) :
    IntegralResult IntegralValue → CallableExecution
  | .ok _ => .normal arguments
  | result => .failed result arguments

/-- Fallthrough walks a finite suffix without consuming the statement depth budget. -/
private def evaluateSwitchClauses
    (evaluate : List IntegralValue → CallableStatement →
      Except CallableEvaluationError CallableExecution)
    (arguments : List IntegralValue) :
    List CallableSwitchClause → Except CallableEvaluationError CallableExecution
  | [] => .ok (.normal arguments)
  | clause :: rest => do
      let result ← evaluate arguments clause.body
      match result with
      | .normal updated => evaluateSwitchClauses evaluate updated rest
      | .break_ updated => pure (.normal updated)
      | .returned _ _ | .failed _ _ | .continue_ _ | .goto_ _ _ => pure result

mutual
  private def evaluateCallArguments (fuel : Nat) (profile : TargetProfile)
      (parameters : List CallableParameter) (arguments : List IntegralValue)
      (expressions : List TypedCallableExpression) :
      Except CallableEvaluationError (IntegralResult (List IntegralValue) × List IntegralValue) :=
    match fuel with
    | 0 => .error .fuelExhausted
    | fuel + 1 =>
        match expressions with
        | [] => .ok (.ok [], arguments)
        | expression :: rest => do
            let (result, updated) ← evaluateTyped fuel profile parameters arguments expression
            match result with
            | .ok value =>
                let (tail, finalArguments) ← evaluateCallArguments fuel profile parameters updated rest
                pure (match tail with
                  | .ok values => .ok (value :: values)
                  | .invalid reason => .invalid reason
                  | .undefined reason => .undefined reason
                  | .unsupported reason => .unsupported reason,
                  finalArguments)
            | result => pure (mapIntegralResultValue result (fun _ => []), updated)

  termination_by structural fuel

  private def evaluateCallableCallee (fuel : Nat) (profile : TargetProfile)
      (callee : CallableCallee) (arguments : List IntegralValue) :
      Except CallableEvaluationError (IntegralResult IntegralValue) := do
    match fuel with
    | 0 => throw .fuelExhausted
    | fuel + 1 =>
        unless profile.valid do throw .invalidProfile
        if callee.signature.result == .void then throw (.unsupportedType .void)
        if arguments.length != callee.parameters.length then throw .arityMismatch
        let converted ← convertArguments profile callee.parameters arguments
        match converted with
        | .ok values =>
            let execution ← evaluateCallableStatement fuel profile callee.parameters values callee.body
            match execution with
            | .normal _ => throw .missingReturn
            | .returned result _ | .failed result _ => pure result
            | .break_ _ => throw .breakOutsideLoop
            | .continue_ _ => throw .continueOutsideLoop
            | .goto_ label _ => throw (.gotoOutsideFunction label)
        | .invalid reason => pure (.invalid reason)
        | .undefined reason => pure (.undefined reason)
        | .unsupported reason => pure (.unsupported reason)

  termination_by structural fuel

  private def evaluateTyped (fuel : Nat) (profile : TargetProfile)
      (parameters : List CallableParameter) (arguments : List IntegralValue)
      (typed : TypedCallableExpression) :
      Except CallableEvaluationError (IntegralResult IntegralValue × List IntegralValue) :=
    match fuel with
    | 0 => .error .fuelExhausted
    | fuel + 1 =>
        match typed.expression with
        | .integer value => (evaluateInteger profile typed value).map (fun result => (result, arguments))
        | .nullPtr => .error (.unsupportedType typed.type)
        | .nullComparison operator =>
            match integralNullComparison operator with
            | some value => pure (.ok value, arguments)
            | none => .error (.unsupportedOperator operator)
        | .sizeOf operandType =>
            (evaluateSizeOf profile typed operandType).map (fun result => (result, arguments))
        | .alignOf operandType =>
            (evaluateAlignOf profile typed operandType).map (fun result => (result, arguments))
        | .noexceptExpr _ => pure (.ok (integralBoolean true), arguments)
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
            let some operation := integralUnaryOfString operator
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
            let some operation := integralLogicalOfString operator
              | .error (.unsupportedOperator operator)
            let (leftResult, afterLeft) ← evaluateTyped fuel profile parameters arguments left
            match leftResult with
            | .ok leftValue =>
                match integralLogicalShortCircuit operation leftValue with
                | some result => pure (.ok result, afterLeft)
                | none =>
                    let (rightResult, afterRight) ←
                      evaluateTyped fuel profile parameters afterLeft right
                    match rightResult with
                    | .ok rightValue =>
                        pure (.ok (integralBoolean (rightValue.value != 0)), afterRight)
                    | result => pure (result, afterRight)
            | result => pure (result, afterLeft)
        | .call callee callArguments => do
            let (argumentResult, afterArguments) ←
              evaluateCallArguments fuel profile parameters arguments callArguments
            match argumentResult with
            | .ok values =>
                let called ← evaluateCallableCallee fuel profile callee values
                match called with
                | .ok value =>
                    let expected ← formatFor profile typed.type
                    if value.format == expected then pure (called, afterArguments)
                    else .error .expressionTypeMismatch
                | result => pure (result, afterArguments)
            | result => pure (mapIntegralResultValue result (fun _ => default), afterArguments)
        | .binary operator left right => do
            if left.expression.hasEffects || right.expression.hasEffects then
              throw .unsequencedEffects
            let some operation := integralBinaryOfString operator
              | .error (.unsupportedOperator operator)
            let (leftResult, _) ← evaluateTyped fuel profile parameters arguments left
            let (rightResult, _) ← evaluateTyped fuel profile parameters arguments right
            match leftResult, rightResult with
            | .ok leftValue, .ok rightValue =>
                let some leftType := integralTypeOfEvidence left.sourceType
                  | throw (.unsupportedType left.sourceType)
                let some rightType := integralTypeOfEvidence right.sourceType
                  | throw (.unsupportedType right.sourceType)
                let result := integralBinaryUsual profile operation leftType rightType
                  leftValue rightValue
                match result with
                | .ok value =>
                    let expected ← formatFor profile typed.type
                    if value.format == expected then pure (result, arguments)
                    else .error .expressionTypeMismatch
                | result => pure (result, arguments)
            | .invalid reason, _ | _, .invalid reason => pure (.invalid reason, arguments)
            | .undefined reason, _ | _, .undefined reason => pure (.undefined reason, arguments)
            | .unsupported reason, _ | _, .unsupported reason => pure (.unsupported reason, arguments)

  termination_by structural fuel
  /-- Iterations exclude the initializer, which the for statement executes once.
  Body completion (including continue through a switch) reaches the step only
  after the body has returned. Inner loops consume their own transfers. -/
  private def evaluateForIterations (fuel : Nat) (profile : TargetProfile)
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
              | .returned _ _ | .failed _ _ | .goto_ _ _ => pure bodyResult
        | result => pure (.failed result afterCondition)

  termination_by structural fuel

  private def evaluateCallableStatement (fuel : Nat) (profile : TargetProfile)
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
      | .cleanups body =>
          evaluateCallableStatement fuel profile parameters arguments body
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
          let some operation := integralCompoundBinaryOfString operator
            | throw (.unsupportedOperator operator)
          let (result, afterExpression) ← evaluateTyped fuel profile parameters arguments expression
          match result with
          | .ok rightValue =>
              let some parameter := parameters.find? (fun parameter =>
                parameter.declaration == declaration)
                | throw (.missingParameter declaration)
              let current ← parameterValue parameters afterExpression declaration
              let some leftType := integralTypeOfEvidence parameter.type
                | throw (.unsupportedType parameter.type)
              let some rightType := integralTypeOfEvidence expression.sourceType
                | throw (.unsupportedType expression.sourceType)
              let combined := integralBinaryUsual profile operation leftType rightType
                current rightValue
              match combined with
              | .ok value =>
                  let stored ← convertTo profile parameter.type value
                  match stored with
                  | .ok value =>
                      match assignParameter profile parameters afterExpression declaration value with
                      | .ok updated => pure (.normal updated)
                      | .error error => throw error
                  | result => pure (.failed result afterExpression)
              | result => pure (.failed result afterExpression)
          | result => pure (.failed result afterExpression)
      | .returnVoid => throw (.unsupportedType .void)
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
              let selected := (callableSwitchCaseSuffix value.value clauses).orElse
                (fun _ => callableSwitchDefaultSuffix clauses) |>.getD []
              evaluateSwitchClauses (evaluateCallableStatement fuel profile parameters)
                afterCondition selected
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
                | .returned _ _ | .failed _ _ | .goto_ _ _ => pure bodyResult
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
          | .returned _ _ | .failed _ _ | .goto_ _ _ => pure bodyResult
      | .forLoop initializer condition step body => do
          let initialResult ← evaluateCallableStatement fuel profile parameters arguments initializer
          match initialResult with
          | .normal updated => evaluateForIterations fuel profile parameters updated condition step body
          | _ => pure initialResult
      | .break_ => pure (.break_ arguments)
      | .continue_ => pure (.continue_ arguments)
      | .goto_ label => pure (.goto_ label arguments)
      | .label _ body => evaluateCallableStatement fuel profile parameters arguments body
      | .sequence first second => do
          let firstResult ← evaluateCallableStatement fuel profile parameters arguments first
          match firstResult with
          | .normal updated => evaluateCallableStatement fuel profile parameters updated second
          | .goto_ label updated =>
              match second.findLabelSuffix label with
              | some suffix => evaluateCallableStatement fuel profile parameters updated suffix
              | none => pure (.goto_ label updated)
          | .returned _ _ | .failed _ _ | .break_ _ | .continue_ _ => pure firstResult

  termination_by structural fuel
end

/-- Argument conversion used by the value evaluator before entering a call. -/
def convertCallableArguments (profile : TargetProfile) (parameters : List CallableParameter)
    (arguments : List IntegralValue) :
    Except CallableEvaluationError (IntegralResult (List IntegralValue)) :=
  convertArguments profile parameters arguments

/-- A single successful conversion is the argument list used by the value
evaluator for a single-parameter call. -/
theorem convertCallableArguments_single (profile : TargetProfile) (parameter : CallableParameter)
    (argument converted : IntegralValue) (fmt : IntegralFormat)
    (hformat : integralFormatOfEvidence profile parameter.type = .ok fmt)
    (hconvert : integralConvert fmt argument = .ok converted) :
    convertCallableArguments profile [parameter] [argument] = .ok (.ok [converted]) := by
  simp [convertCallableArguments, convertArguments, convertTo, integralConvertOfEvidence,
    hformat, hconvert, Except.bind, Bind.bind, Except.mapError, Pure.pure, Except.pure]

/-- The value evaluator's expression boundary, including the updated
parameter values. This is the same evaluator used inside callable bodies. -/
def evaluateCallableExpression (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments : List IntegralValue)
    (expression : TypedCallableExpression) :
    Except CallableEvaluationError (IntegralResult IntegralValue × List IntegralValue) :=
  evaluateTyped fuel profile parameters arguments expression

/-- A successful condition selects one branch after retaining its effects. -/
theorem evaluateCallableExpression_conditional (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments afterCondition afterBranch : List IntegralValue)
    (condition whenTrue whenFalse : TypedCallableExpression)
    (sourceType resultType : CppTypeEvidence) (value : IntegralValue)
    (result : IntegralResult IntegralValue)
    (hcond : evaluateCallableExpression fuel profile parameters arguments condition =
      .ok (.ok value, afterCondition))
    (hbranch : evaluateCallableExpression fuel profile parameters afterCondition
      (if value.value == 0 then whenFalse else whenTrue) = .ok (result, afterBranch)) :
    evaluateCallableExpression (fuel + 1) profile parameters arguments
      {expression := .conditional condition whenTrue whenFalse,
       sourceType := sourceType, type := resultType} = .ok (result, afterBranch) := by
  simp only [evaluateCallableExpression] at hcond hbranch
  by_cases hz : value.value = 0 <;>
    simpa [evaluateCallableExpression, evaluateTyped, hcond, hz,
      Except.bind, Bind.bind] using hbranch

/-- A non-value condition propagates without evaluating either branch. -/
theorem evaluateCallableExpression_conditional_nonvalue (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments afterCondition : List IntegralValue)
    (condition whenTrue whenFalse : TypedCallableExpression)
    (sourceType resultType : CppTypeEvidence) (result : IntegralResult IntegralValue)
    (hnonvalue : ∀ v, result ≠ .ok v)
    (hcond : evaluateCallableExpression fuel profile parameters arguments condition =
      .ok (result, afterCondition)) :
    evaluateCallableExpression (fuel + 1) profile parameters arguments
      {expression := .conditional condition whenTrue whenFalse,
       sourceType := sourceType, type := resultType} = .ok (result, afterCondition) := by
  simp only [evaluateCallableExpression] at hcond
  cases result with
  | ok v => exact False.elim (hnonvalue v rfl)
  | invalid reason =>
      simp [evaluateCallableExpression, evaluateTyped, hcond, Except.bind, Bind.bind, Pure.pure, Except.pure]
  | undefined reason =>
      simp [evaluateCallableExpression, evaluateTyped, hcond, Except.bind, Bind.bind, Pure.pure, Except.pure]
  | unsupported reason =>
      simp [evaluateCallableExpression, evaluateTyped, hcond, Except.bind, Bind.bind, Pure.pure, Except.pure]

/-- A resolved conversion applies to an operand result and keeps the argument
state produced by that operand. -/
theorem evaluateCallableExpression_convert (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments arguments' : List IntegralValue)
    (operand : TypedCallableExpression) (sourceType resultType : CppTypeEvidence)
    (fmt : IntegralFormat) (result : IntegralResult IntegralValue)
    (hoperand : evaluateCallableExpression fuel profile parameters arguments operand =
      .ok (result, arguments'))
    (hformat : integralFormatOfEvidence profile resultType = .ok fmt) :
    evaluateCallableExpression (fuel + 1) profile parameters arguments
      {expression := .convert operand, sourceType := sourceType, type := resultType} =
      .ok (bindIntegralResultValue result (integralConvert fmt), arguments') := by
  simp only [evaluateCallableExpression] at hoperand
  cases result <;>
    simp [evaluateCallableExpression, evaluateTyped, hoperand, convertTo,
      integralConvertOfEvidence, hformat, bindIntegralResultValue, Except.mapError,
      Except.map, Except.bind, Bind.bind, Pure.pure, Except.pure]

/-- A literal leaves arguments unchanged; self-conversion expresses both its
valid result and its invalid-value result. -/
theorem evaluateCallableExpression_literal (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments : List IntegralValue)
    (n : Nat) (value : IntegralValue) (sourceType resultType : CppTypeEvidence)
    (hsource : integralLiteralOfEvidence profile sourceType n = .ok value) :
    evaluateCallableExpression (fuel + 1) profile parameters arguments
      {expression := .integer n, sourceType := sourceType, type := resultType} =
      .ok (integralConvert value.format value, arguments) := by
  cases hvalid : value.invalid? with
  | none =>
      simp [evaluateCallableExpression, evaluateTyped, evaluateInteger, hsource,
        Except.mapError, Except.map, Functor.map, hvalid, integralConvert_same]
  | some reason =>
      simp [evaluateCallableExpression, evaluateTyped, evaluateInteger, hsource,
        Except.mapError, Except.map, Functor.map, hvalid, integralConvert_same]

/-- Reading a valid parameter whose selected types have its format returns the
value without changing the argument list. -/
theorem evaluateCallableExpression_parameter (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments : List IntegralValue)
    (declaration : FrontendHandle) (index : Nat) (param : CallableParameter)
    (value : IntegralValue) (sourceType resultType : CppTypeEvidence)
    (hidx : parameters.findIdx? (fun p => p.declaration == declaration) = some index)
    (hp : parameters[index]? = some param) (ha : arguments[index]? = some value)
    (hparam : integralFormatOfEvidence profile param.type = .ok value.format)
    (hresult : integralFormatOfEvidence profile resultType = .ok value.format)
    (hvalid : value.invalid? = none) :
    evaluateCallableExpression (fuel + 1) profile parameters arguments
      {expression := .parameter declaration, sourceType := sourceType, type := resultType} =
      .ok (.ok value, arguments) := by
  have heq : (value.format == value.format) = true := by
    cases value.format <;> simp [BEq.beq, instBEqIntegralFormat.beq]
  simp [evaluateCallableExpression, evaluateTyped, evaluateParameter, hidx, hp, argumentAt, ha,
    exactArgument, formatFor, hparam, convertTo, integralConvertOfEvidence, hresult,
    Except.mapError, Except.map, Except.bind, Bind.bind, Pure.pure, Except.pure, heq,
    integralConvert_same_of_valid, hvalid]

def evaluateCallableValue (fuel : Nat) (profile : TargetProfile) (function : CallableFunction)
    (arguments : List IntegralValue) :
    Except CallableEvaluationError (IntegralResult IntegralValue) := do
  unless profile.valid do throw .invalidProfile
  if function.signature.result == .void then throw (.unsupportedType .void)
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
      | .goto_ label _ => .error (.gotoOutsideFunction label)
  | .invalid reason => pure (.invalid reason)
  | .undefined reason => pure (.undefined reason)
  | .unsupported reason => pure (.unsupported reason)


/-- A no-parameter return delegates to the value expression evaluator. -/
theorem evaluateCallable_return_noParameters (fuel : Nat) (profile : TargetProfile) (function : CallableFunction)
    (expression : TypedCallableExpression) (result : IntegralResult IntegralValue)
    (hvalid : profile.valid = true) (hresult : (function.signature.result == .void) = false)
    (hparams : function.parameters = []) (hbody : function.body = .return_ expression)
    (hexpr : evaluateCallableExpression fuel profile [] [] expression = .ok (result, [])) :
    evaluateCallableValue (fuel + 1) profile function [] = .ok result := by
  simp only [evaluateCallableExpression] at hexpr
  simp [evaluateCallableValue, hvalid, hresult, hparams, hbody, convertArguments,
    evaluateCallableStatement, hexpr, Except.map, Except.bind, Bind.bind]


/-- A no-parameter block return delegates to the value expression evaluator. -/
theorem evaluateCallable_blockReturn_noParameters (fuel : Nat) (profile : TargetProfile) (function : CallableFunction)
    (expression : TypedCallableExpression) (result : IntegralResult IntegralValue)
    (hvalid : profile.valid = true) (hresult : (function.signature.result == .void) = false)
    (hparams : function.parameters = []) (hbody : function.body = .block (.return_ expression))
    (hexpr : evaluateCallableExpression fuel profile [] [] expression = .ok (result, [])) :
    evaluateCallableValue (fuel + 2) profile function [] = .ok result := by
  simp only [evaluateCallableExpression] at hexpr
  simp [evaluateCallableValue, hvalid, hresult, hparams, hbody, convertArguments,
    evaluateCallableStatement, hexpr, Except.map, Except.bind, Bind.bind]

end LeanModels.Cpp
