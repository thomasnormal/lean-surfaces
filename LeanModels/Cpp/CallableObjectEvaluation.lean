import LeanModels.Cpp.CallableFrame
import LeanModels.Cpp.ScalarArithmetic

namespace LeanModels.Cpp

inductive CallableObjectEvaluationError where
  | invalidProfile
  | arityMismatch
  | invalidArgument (reason : InvalidIntegral)
  | undefinedArgument (reason : IntegralUB)
  | unsupportedArgument (reason : IntegralUnsupported)
  | argumentTypeMismatch (declaration : FrontendHandle)
  | unsupportedOperator (operator : String)
  | unsupportedCall
  | voidResultRequiresResultAPI
  | returnTypeMismatch
  | missingReturn
  | breakOutsideLoop
  | continueOutsideLoop
  | gotoOutsideFunction (label : String)
  | frameError (reason : FrameError)
  deriving Repr, BEq, Inhabited

namespace CallableObjectEvaluation

structure Outcome (α : Type) where
  frame : IntegralObjectFrame
  result : Except CallableObjectEvaluationError α
  deriving Inhabited

private def success (frame : IntegralObjectFrame) (value : α) : Outcome α :=
  {frame, result := .ok value}

private def failure (frame : IntegralObjectFrame) (reason : CallableObjectEvaluationError) :
    Outcome α :=
  {frame, result := .error reason}

private def mapFrameError (reason : FrameError) : CallableObjectEvaluationError :=
  .frameError reason

private def frameFailure (frame : IntegralObjectFrame) (reason : FrameError) :
    Outcome α :=
  failure frame (mapFrameError reason)

private def formatFor (profile : TargetProfile) (type : CppTypeEvidence) :
    Option IntegralFormat :=
  (integralFormatOfEvidence profile type).toOption

private def mapOutcome (outcome : Outcome (IntegralResult IntegralValue))
    (convert : IntegralValue → IntegralResult IntegralValue) :
    Outcome (IntegralResult IntegralValue) :=
  match outcome.result with
  | .error reason => failure outcome.frame reason
  | .ok result => success outcome.frame (bindIntegralResultValue result convert)

private def convertTo (profile : TargetProfile) (type : CppTypeEvidence)
    (value : IntegralValue) : IntegralResult IntegralValue :=
  match integralConvertOfEvidence profile type value with
  | .ok result => result
  | .error _ => .unsupported .unresolvedArithmeticConversions

private def literalValue (profile : TargetProfile) (typed : TypedCallableExpression) (value : Nat) :
    Option IntegralValue :=
  (integralLiteralOfEvidence profile typed.sourceType value).toOption

private def sizeOfValue (profile : TargetProfile) (typed : TypedCallableExpression)
    (operandType : CppTypeEvidence) : IntegralResult IntegralValue :=
  match integralSizeValueOfEvidence profile typed.type operandType with
  | .ok value => .ok value
  | .error _ => .unsupported .unresolvedArithmeticConversions

private def alignOfValue (profile : TargetProfile) (typed : TypedCallableExpression)
    (operandType : CppTypeEvidence) : IntegralResult IntegralValue :=
  match integralAlignValueOfEvidence profile typed.type operandType with
  | .ok value => .ok value
  | .error _ => .unsupported .unresolvedArithmeticConversions

private inductive Execution where
  | normal
  | returnedVoid
  | returned (result : IntegralResult IntegralValue)
  | failed (result : IntegralResult IntegralValue)
  | break_
  | continue_
  | goto_ (label : String)
  deriving Inhabited

private def finishResult (frame : IntegralObjectFrame)
    (result : IntegralResult IntegralValue) : Outcome Execution :=
  match result with
  | .ok _ => success frame .normal
  | _ => success frame (.failed result)

private def incrementValue (profile : TargetProfile) (type : CppTypeEvidence)
    (operation : IntegralBinary) (old : IntegralValue) : IntegralResult IntegralValue :=
  integralIncrementValue profile type operation old

private def evalParameter (fuel : Nat) (profile : TargetProfile)
    (frame : IntegralObjectFrame) (typed : TypedCallableExpression)
    (declaration : FrontendHandle) : Outcome (IntegralResult IntegralValue) :=
  match fuel with
  | 0 => frameFailure frame .fuelExhausted
  | fuel + 1 =>
      let read := frame.evaluate fuel (.read declaration)
      match read.result with
      | .error reason => frameFailure read.frame reason
      | .ok result => success read.frame (bindIntegralResultValue result (convertTo profile typed.type))

private def evalIncrement (fuel : Nat) (profile : TargetProfile)
    (frame : IntegralObjectFrame) (typed : TypedCallableExpression)
    (operator : String) (isPostfix : Bool) (declaration : FrontendHandle) :
    Outcome (IntegralResult IntegralValue) :=
  match integralIncrementBinaryOfString operator with
  | some operation =>
      let current := evalParameter fuel profile frame typed declaration
      match current.result with
      | .error reason => failure current.frame reason
      | .ok result =>
          match result with
          | .ok old =>
              match current.frame.lookup declaration with
              | .error reason => frameFailure current.frame reason
              | .ok binding =>
                  match incrementValue profile binding.type operation old with
                  | .ok value =>
                      let assigned := current.frame.assignValue declaration binding.type value
                      match assigned.result with
                      | .error reason => frameFailure assigned.frame reason
                      | .ok _ =>
                          success assigned.frame (convertTo profile typed.type
                            (if isPostfix then old else value))
                  | result =>
                      success current.frame
                        (bindIntegralResultValue result (convertTo profile typed.type))
          | result =>
              success current.frame (bindIntegralResultValue result (convertTo profile typed.type))
  | none => failure frame (.unsupportedOperator operator)

private def evalExpression (fuel : Nat) (profile : TargetProfile)
    (frame : IntegralObjectFrame) (typed : TypedCallableExpression) :
    Outcome (IntegralResult IntegralValue) :=
  match fuel with
  | 0 => frameFailure frame .fuelExhausted
  | fuel + 1 =>
      match typed.expression with
      | .integer value =>
          match literalValue profile typed value with
          | none => success frame (.unsupported .unresolvedArithmeticConversions)
          | some value => success frame (convertTo profile typed.type value)
      | .nullPtr => success frame (.unsupported .unresolvedArithmeticConversions)
      | .nullComparison operator =>
          match integralNullComparison operator with
          | some value => success frame (.ok value)
          | none => success frame (.unsupported .unresolvedArithmeticConversions)
      | .sizeOf operandType =>
          success frame (sizeOfValue profile typed operandType)
      | .alignOf operandType =>
          success frame (alignOfValue profile typed operandType)
      | .noexceptExpr _ => success frame (.ok (integralBoolean true))
      | .parameter declaration =>
          evalParameter (fuel + 1) profile frame typed declaration
      | .increment operator isPostfix declaration =>
          evalIncrement fuel profile frame typed operator isPostfix declaration
      | .convert operand =>
          mapOutcome (evalExpression fuel profile frame operand)
            (convertTo profile typed.type)
      | .unary operator operand =>
          match integralUnaryOfString operator with
          | none => success frame (.unsupported .unresolvedArithmeticConversions)
          | some operation =>
              let evaluated := evalExpression fuel profile frame operand
              match evaluated.result with
              | .error reason => failure evaluated.frame reason
              | .ok result =>
                  success evaluated.frame (bindIntegralResultValue result fun value =>
                    bindIntegralResultValue (integralUnary operation value)
                      (convertTo profile typed.type))
      | .binary operator left right =>
          match integralBinaryOfString operator with
          | none => success frame (.unsupported .unresolvedArithmeticConversions)
          | some operation =>
              if left.expression.hasEffects || right.expression.hasEffects then
                success frame (.unsupported .unresolvedArithmeticConversions)
              else
                let leftResult := evalExpression fuel profile frame left
                match leftResult.result with
                | .error reason => failure leftResult.frame reason
                | .ok leftValue =>
                    let rightResult := evalExpression fuel profile leftResult.frame right
                    match rightResult.result with
                    | .error reason => failure rightResult.frame reason
                    | .ok rightValue =>
                        let combined := match leftValue, rightValue with
                          | .ok leftValue, .ok rightValue =>
                              match integralTypeOfEvidence left.sourceType,
                                  integralTypeOfEvidence right.sourceType with
                              | some leftType, some rightType =>
                                  integralBinaryUsual profile operation leftType rightType
                                    leftValue rightValue
                              | _, _ => .unsupported .unresolvedArithmeticConversions
                          | .invalid reason, _ | _, .invalid reason => .invalid reason
                          | .undefined reason, _ | _, .undefined reason => .undefined reason
                          | .unsupported reason, _ | _, .unsupported reason =>
                              .unsupported reason
                        success rightResult.frame
                          (bindIntegralResultValue combined (convertTo profile typed.type))
      | .conditional condition whenTrue whenFalse =>
          let conditionResult := evalExpression fuel profile frame condition
          match conditionResult.result with
          | .error reason => failure conditionResult.frame reason
          | .ok (.ok value) =>
              if value.value == 0 then
                evalExpression fuel profile conditionResult.frame whenFalse
              else
                evalExpression fuel profile conditionResult.frame whenTrue
          | .ok result => success conditionResult.frame result
      | .comma left right =>
          let leftResult := evalExpression fuel profile frame left
          match leftResult.result with
          | .error reason => failure leftResult.frame reason
          | .ok (.ok _) => evalExpression fuel profile leftResult.frame right
          | .ok result => success leftResult.frame result
      | .logical operator left right =>
          match integralLogicalOfString operator with
          | some operation =>
              let leftResult := evalExpression fuel profile frame left
              match leftResult.result with
              | .error reason => failure leftResult.frame reason
              | .ok (.ok value) =>
                  match integralLogicalShortCircuit operation value with
                  | some result => success leftResult.frame (.ok result)
                  | none =>
                      let rightResult := evalExpression fuel profile leftResult.frame right
                      match rightResult.result with
                      | .error reason => failure rightResult.frame reason
                      | .ok (.ok rightValue) =>
                          success rightResult.frame
                            (.ok (integralBoolean (rightValue.value != 0)))
                      | .ok result => success rightResult.frame result
              | .ok result => success leftResult.frame result
          | none => success frame (.unsupported .unresolvedArithmeticConversions)
      | .call _ _ => failure frame .unsupportedCall
termination_by structural fuel

/-- The object evaluator's expression boundary, retaining the resulting
frame. This is the same evaluator used inside callable bodies. -/
def evaluateCallableObjectExpression (fuel : Nat) (profile : TargetProfile)
    (frame : IntegralObjectFrame) (expression : TypedCallableExpression) :
    Outcome (IntegralResult IntegralValue) :=
  evalExpression fuel profile frame expression

/-- A successful condition selects one branch after retaining its effects. -/
theorem evaluateCallableObjectExpression_conditional (fuel : Nat) (profile : TargetProfile)
    (frame afterCondition afterBranch : IntegralObjectFrame)
    (condition whenTrue whenFalse : TypedCallableExpression)
    (sourceType resultType : CppTypeEvidence) (value : IntegralValue)
    (result : IntegralResult IntegralValue)
    (hcond : evaluateCallableObjectExpression fuel profile frame condition =
      {frame := afterCondition, result := .ok (.ok value)})
    (hbranch : evaluateCallableObjectExpression fuel profile afterCondition
      (if value.value == 0 then whenFalse else whenTrue) =
      {frame := afterBranch, result := .ok result}) :
    evaluateCallableObjectExpression (fuel + 1) profile frame
      {expression := .conditional condition whenTrue whenFalse,
       sourceType := sourceType, type := resultType} =
      {frame := afterBranch, result := .ok result} := by
  simp only [evaluateCallableObjectExpression] at hcond hbranch
  by_cases hz : value.value = 0 <;>
    simpa [evaluateCallableObjectExpression, evalExpression, hcond, hz] using hbranch

/-- A non-value condition propagates without evaluating either branch. -/
theorem evaluateCallableObjectExpression_conditional_nonvalue (fuel : Nat) (profile : TargetProfile)
    (frame afterCondition : IntegralObjectFrame)
    (condition whenTrue whenFalse : TypedCallableExpression)
    (sourceType resultType : CppTypeEvidence) (result : IntegralResult IntegralValue)
    (hnonvalue : ∀ v, result ≠ .ok v)
    (hcond : evaluateCallableObjectExpression fuel profile frame condition =
      {frame := afterCondition, result := .ok result}) :
    evaluateCallableObjectExpression (fuel + 1) profile frame
      {expression := .conditional condition whenTrue whenFalse,
       sourceType := sourceType, type := resultType} =
      {frame := afterCondition, result := .ok result} := by
  simp only [evaluateCallableObjectExpression] at hcond
  cases result with
  | ok v => exact False.elim (hnonvalue v rfl)
  | invalid reason => simp [evaluateCallableObjectExpression, evalExpression, hcond, success]
  | undefined reason => simp [evaluateCallableObjectExpression, evalExpression, hcond, success]
  | unsupported reason => simp [evaluateCallableObjectExpression, evalExpression, hcond, success]

/-- A resolved conversion applies to an operand result and keeps the frame
produced by that operand. -/
theorem evaluateCallableObjectExpression_convert (fuel : Nat) (profile : TargetProfile)
    (frame frame' : IntegralObjectFrame) (operand : TypedCallableExpression)
    (sourceType resultType : CppTypeEvidence) (fmt : IntegralFormat)
    (result : IntegralResult IntegralValue)
    (hoperand : evaluateCallableObjectExpression fuel profile frame operand =
      {frame := frame', result := .ok result})
    (hformat : integralFormatOfEvidence profile resultType = .ok fmt) :
    evaluateCallableObjectExpression (fuel + 1) profile frame
      {expression := .convert operand, sourceType := sourceType, type := resultType} =
      {frame := frame', result := .ok (bindIntegralResultValue result (integralConvert fmt))} := by
  simp only [evaluateCallableObjectExpression] at hoperand
  cases result <;>
    simp [evaluateCallableObjectExpression, evalExpression, hoperand, mapOutcome, success,
      bindIntegralResultValue, convertTo, integralConvertOfEvidence, hformat,
      Except.bind, Bind.bind, Pure.pure, Except.pure]

/-- A literal preserves the frame and converts the constructed value to the
selected result format. -/
theorem evaluateCallableObjectExpression_literal (fuel : Nat) (profile : TargetProfile)
    (frame : IntegralObjectFrame) (n : Nat) (value : IntegralValue)
    (sourceType resultType : CppTypeEvidence)
    (hsource : integralLiteralOfEvidence profile sourceType n = .ok value)
    (hresult : integralFormatOfEvidence profile resultType = .ok value.format) :
    evaluateCallableObjectExpression (fuel + 1) profile frame
      {expression := .integer n, sourceType := sourceType, type := resultType} =
      {frame := frame, result := .ok (integralConvert value.format value)} := by
  simp [evaluateCallableObjectExpression, evalExpression, literalValue, hsource, success,
    convertTo, integralConvertOfEvidence, hresult, Except.bind, Bind.bind, Pure.pure,
    Except.pure, Except.toOption]

/-- A parameter read that the frame resolves to a valid value of the selected
format returns that value without changing the frame. -/
theorem evaluateCallableObjectExpression_parameter (fuel : Nat) (profile : TargetProfile)
    (frame : IntegralObjectFrame) (declaration : FrontendHandle) (value : IntegralValue)
    (sourceType resultType : CppTypeEvidence)
    (hread : frame.evaluate 1 (.read declaration) =
      {frame := frame, result := .ok (.ok value)})
    (hformat : integralFormatOfEvidence profile resultType = .ok value.format)
    (hvalid : value.invalid? = none) :
    evaluateCallableObjectExpression (fuel + 2) profile frame
      {expression := .parameter declaration, sourceType := sourceType, type := resultType} =
      {frame := frame, result := .ok (.ok value)} := by
  have hread' : frame.evaluate (fuel + 1) (.read declaration) =
      {frame := frame, result := .ok (.ok value)} := hread
  simp [evaluateCallableObjectExpression, evalExpression, evalParameter, hread', success, convertTo,
    integralConvertOfEvidence, hformat, bindIntegralResultValue, integralConvert_same_of_valid,
    Bind.bind, Pure.pure, Except.bind, Except.pure, hvalid]

/-- The callback already has smaller fuel; fallthrough itself descends the clause list. -/
private def evalSwitch
    (evaluate : IntegralObjectFrame → CallableStatement → Outcome Execution)
    (frame : IntegralObjectFrame) : List CallableSwitchClause → Outcome Execution
  | [] => success frame .normal
  | clause :: rest =>
      let current := evaluate frame clause.body
      match current.result with
      | .error reason => failure current.frame reason
      | .ok .normal => evalSwitch evaluate current.frame rest
      | .ok .break_ => success current.frame .normal
      | .ok execution => success current.frame execution

private def evalSwitchItems
    (evaluate : IntegralObjectFrame → CallableStatement → Outcome Execution)
    (frame : IntegralObjectFrame) : List CallableSwitchItem → Outcome Execution
  | [] => success frame .normal
  | item :: rest =>
      let body := match item with
        | .statement _ body | .case_ _ _ body | .default_ _ body => body
      let current := evaluate frame body
      match current.result with
      | .error reason => failure current.frame reason
      | .ok .normal => evalSwitchItems evaluate current.frame rest
      | .ok .break_ => success current.frame .normal
      | .ok execution => success current.frame execution

private def callableSwitchItemCaseSuffix (value : Int) :
    List CallableSwitchItem → Option (List CallableSwitchItem)
  | [] => none
  | item :: rest =>
      match item with
      | .case_ _ label _ =>
          if label == value then some (item :: rest)
          else callableSwitchItemCaseSuffix value rest
      | .statement _ _ | .default_ _ _ => callableSwitchItemCaseSuffix value rest

private def callableSwitchItemDefaultSuffix : List CallableSwitchItem →
    Option (List CallableSwitchItem)
  | [] => none
  | item :: rest =>
      match item with
      | .default_ _ _ => some (item :: rest)
      | .statement _ _ | .case_ _ _ _ => callableSwitchItemDefaultSuffix rest

mutual
  private def evalStatement (fuel : Nat) (profile : TargetProfile)
      (frame : IntegralObjectFrame) (statement : CallableStatement) :
      Outcome Execution :=
    match fuel with
    | 0 => frameFailure frame .fuelExhausted
    | fuel + 1 =>
        match statement with
        | .skip => success frame .normal
        | .automatic declaration =>
            let result := frame.executeOpen fuel declaration.statement
            match result.result with
            | .error reason => frameFailure result.frame reason
            | .ok none => success result.frame .normal
            | .ok (some value) => success result.frame (.returned (.ok value))
        | .block body =>
            let entered := frame.enterScope
            match entered.result with
            | .error reason => frameFailure entered.frame reason
            | .ok _ =>
                let bodyResult := evalStatement fuel profile entered.frame body
                match bodyResult.result with
                | .error reason => failure bodyResult.frame reason
                | .ok execution =>
                    let exited := bodyResult.frame.exitScope
                    match exited.result with
                    | .error reason => frameFailure exited.frame reason
                    | .ok _ => success exited.frame execution
        | .cleanups body =>
            evalStatement fuel profile frame body
        | .expression expression =>
            let result := evalExpression fuel profile frame expression
            match result.result with
            | .error reason => failure result.frame reason
            | .ok value => finishResult result.frame value
        | .assign declaration expression =>
            let evaluated := evalExpression fuel profile frame expression
            match evaluated.result with
            | .error reason => failure evaluated.frame reason
            | .ok (.ok value) =>
                match evaluated.frame.lookup declaration with
                | .error reason => frameFailure evaluated.frame reason
                | .ok binding =>
                    let assigned := evaluated.frame.assignValue declaration binding.type value
                    match assigned.result with
                    | .error reason => frameFailure assigned.frame reason
                    | .ok _ => success assigned.frame .normal
            | .ok result => success evaluated.frame (.failed result)
        | .compoundAssign operator declaration expression =>
            match integralCompoundBinaryOfString operator with
            | none => failure frame (.unsupportedOperator operator)
            | some operation =>
                let evaluated := evalExpression fuel profile frame expression
                match evaluated.result with
                | .error reason => failure evaluated.frame reason
                | .ok (.ok rightValue) =>
                    match evaluated.frame.lookup declaration with
                    | .error reason => frameFailure evaluated.frame reason
                    | .ok binding =>
                        match evaluated.frame.evaluate 1 (.read declaration) with
                        | read =>
                            match read.result with
                            | .error reason => frameFailure read.frame reason
                            | .ok (.ok current) =>
                                let combined := match integralTypeOfEvidence binding.type,
                                    integralTypeOfEvidence expression.sourceType with
                                  | some leftType, some rightType =>
                                      bindIntegralResultValue
                                        (integralBinaryUsual profile operation leftType rightType
                                          current rightValue)
                                        (fun value => convertTo profile binding.type value)
                                  | _, _ => .unsupported .unresolvedArithmeticConversions
                                match combined with
                                | .ok value =>
                                    let assigned := read.frame.assignValue declaration binding.type value
                                    match assigned.result with
                                    | .error reason => frameFailure assigned.frame reason
                                    | .ok _ => success assigned.frame .normal
                                | result => success read.frame (.failed result)
                            | .ok result => success read.frame (.failed result)
                | .ok result => success evaluated.frame (.failed result)
        | .returnVoid => success frame .returnedVoid
        | .return_ expression =>
            let evaluated := evalExpression fuel profile frame expression
            match evaluated.result with
            | .error reason => failure evaluated.frame reason
            | .ok (.ok value) => success evaluated.frame (.returned (.ok value))
            | .ok result => success evaluated.frame (.failed result)
        | .goto_ label => success frame (.goto_ label)
        | .label _ body => evalStatement fuel profile frame body
        | .conditional condition whenTrue whenFalse =>
            let evaluated := evalExpression fuel profile frame condition
            match evaluated.result with
            | .error reason => failure evaluated.frame reason
            | .ok (.ok value) =>
                evalStatement fuel profile evaluated.frame (if value.value == 0 then whenFalse else whenTrue)
            | .ok result => success evaluated.frame (.failed result)
        | .switch_ condition clauses =>
            let evaluated := evalExpression fuel profile frame condition
            match evaluated.result with
            | .error reason => failure evaluated.frame reason
            | .ok (.ok value) =>
                let entered := evaluated.frame.enterScope
                match entered.result with
                | .error reason => frameFailure entered.frame reason
                | .ok _ =>
                    let selected := (callableSwitchCaseSuffix value.value clauses).orElse
                      (fun _ => callableSwitchDefaultSuffix clauses) |>.getD []
                    let switched := evalSwitch (evalStatement fuel profile) entered.frame selected
                    match switched.result with
                    | .error reason => failure switched.frame reason
                    | .ok execution =>
                        let exited := switched.frame.exitScope
                        match exited.result with
                        | .error reason => frameFailure exited.frame reason
                        | .ok _ => success exited.frame execution
            | .ok result => success evaluated.frame (.failed result)
        | .switchItems_ condition items =>
            let evaluated := evalExpression fuel profile frame condition
            match evaluated.result with
            | .error reason => failure evaluated.frame reason
            | .ok (.ok value) =>
                let entered := evaluated.frame.enterScope
                match entered.result with
                | .error reason => frameFailure entered.frame reason
                | .ok _ =>
                    let selected := (callableSwitchItemCaseSuffix value.value items).orElse
                      (fun _ => callableSwitchItemDefaultSuffix items) |>.getD []
                    let switched := evalSwitchItems (evalStatement fuel profile) entered.frame selected
                    match switched.result with
                    | .error reason => failure switched.frame reason
                    | .ok execution =>
                        let exited := switched.frame.exitScope
                        match exited.result with
                        | .error reason => frameFailure exited.frame reason
                        | .ok _ => success exited.frame execution
            | .ok result => success evaluated.frame (.failed result)
        | .whileLoop condition body => evalWhile fuel profile frame condition body
        | .doWhile body condition => evalDoWhile fuel profile frame body condition
        | .forLoop initializer condition step body =>
            let entered := frame.enterScope
            match entered.result with
            | .error reason => frameFailure entered.frame reason
            | .ok _ =>
                let initial := evalStatement fuel profile entered.frame initializer
                match initial.result with
                | .error reason => failure initial.frame reason
                | .ok .normal =>
                    let looped := evalFor fuel profile initial.frame condition step body
                    match looped.result with
                    | .error reason => failure looped.frame reason
                    | .ok execution =>
                        let exited := looped.frame.exitScope
                        match exited.result with
                        | .error reason => frameFailure exited.frame reason
                        | .ok _ => success exited.frame execution
                | .ok execution =>
                    let exited := initial.frame.exitScope
                    match exited.result with
                    | .error reason => frameFailure exited.frame reason
                    | .ok _ => success exited.frame execution
        | .break_ => success frame .break_
        | .continue_ => success frame .continue_
        | .sequence first second =>
            let firstResult := evalStatement fuel profile frame first
            match firstResult.result with
            | .error reason => failure firstResult.frame reason
            | .ok .normal => evalStatement fuel profile firstResult.frame second
            | .ok (.goto_ label) =>
                match second.findLabelSuffix label with
                | some suffix => evalStatement fuel profile firstResult.frame suffix
                | none => success firstResult.frame (.goto_ label)
            | .ok execution => success firstResult.frame execution

  termination_by structural fuel

  private def evalWhile (fuel : Nat) (profile : TargetProfile)
      (frame : IntegralObjectFrame) (condition : TypedCallableExpression)
      (body : CallableStatement) : Outcome Execution :=
    match fuel with
    | 0 => frameFailure frame .fuelExhausted
    | fuel + 1 =>
        let evaluated := evalExpression fuel profile frame condition
        match evaluated.result with
        | .error reason => failure evaluated.frame reason
        | .ok (.ok value) =>
            if value.value == 0 then success evaluated.frame .normal
            else
              let bodyResult := evalStatement fuel profile evaluated.frame body
              match bodyResult.result with
              | .error reason => failure bodyResult.frame reason
              | .ok .normal | .ok .continue_ => evalWhile fuel profile bodyResult.frame condition body
              | .ok .break_ => success bodyResult.frame .normal
              | .ok execution => success bodyResult.frame execution
        | .ok result => success evaluated.frame (.failed result)

  termination_by structural fuel

  private def evalDoWhile (fuel : Nat) (profile : TargetProfile)
      (frame : IntegralObjectFrame) (body : CallableStatement)
      (condition : TypedCallableExpression) : Outcome Execution :=
    match fuel with
    | 0 => frameFailure frame .fuelExhausted
    | fuel + 1 =>
        let bodyResult := evalStatement fuel profile frame body
        match bodyResult.result with
        | .error reason => failure bodyResult.frame reason
        | .ok .break_ => success bodyResult.frame .normal
        | .ok (.goto_ label) => success bodyResult.frame (.goto_ label)
        | .ok .returnedVoid => success bodyResult.frame .returnedVoid
        | .ok (.returned result) => success bodyResult.frame (.returned result)
        | .ok (.failed result) => success bodyResult.frame (.failed result)
        | .ok .normal | .ok .continue_ =>
            let conditionResult := evalExpression fuel profile bodyResult.frame condition
            match conditionResult.result with
            | .error reason => failure conditionResult.frame reason
            | .ok (.ok value) =>
                if value.value == 0 then success conditionResult.frame .normal
                else evalDoWhile fuel profile conditionResult.frame body condition
            | .ok result => success conditionResult.frame (.failed result)

  termination_by structural fuel

  private def evalFor (fuel : Nat) (profile : TargetProfile)
      (frame : IntegralObjectFrame) (condition : TypedCallableExpression)
      (step body : CallableStatement) : Outcome Execution :=
    match fuel with
    | 0 => frameFailure frame .fuelExhausted
    | fuel + 1 =>
        let conditionResult := evalExpression fuel profile frame condition
        match conditionResult.result with
        | .error reason => failure conditionResult.frame reason
        | .ok (.ok value) =>
            if value.value == 0 then success conditionResult.frame .normal
            else
              let bodyResult := evalStatement fuel profile conditionResult.frame body
              match bodyResult.result with
              | .error reason => failure bodyResult.frame reason
              | .ok .break_ => success bodyResult.frame .normal
              | .ok (.goto_ label) => success bodyResult.frame (.goto_ label)
              | .ok .returnedVoid => success bodyResult.frame .returnedVoid
              | .ok (.returned result) =>
                  success bodyResult.frame (.returned result)
              | .ok (.failed result) =>
                  success bodyResult.frame (.failed result)
              | .ok .normal | .ok .continue_ =>
                  let stepResult := evalStatement fuel profile bodyResult.frame step
                  match stepResult.result with
                  | .error reason => failure stepResult.frame reason
                  | .ok .normal | .ok .continue_ =>
                      evalFor fuel profile stepResult.frame condition step body
                  | .ok execution => success stepResult.frame execution
        | .ok result => success conditionResult.frame (.failed result)
  termination_by structural fuel

end

private def liftIntegralResult : IntegralResult IntegralValue →
    IntegralResult (Option IntegralValue)
  | .ok value => .ok (some value)
  | .invalid reason => .invalid reason
  | .undefined reason => .undefined reason
  | .unsupported reason => .unsupported reason

private def closeResult (frame : IntegralObjectFrame)
    (result : IntegralResult (Option IntegralValue)) :
    Outcome (IntegralResult (Option IntegralValue)) :=
  let closed := frame.leaveFrame
  match closed.result with
  | .error reason => frameFailure closed.frame reason
  | .ok _ => success closed.frame result

private def closeCallable (resultType : CppTypeEvidence) (outcome : Outcome Execution) :
    Outcome (IntegralResult (Option IntegralValue)) :=
  match outcome.result with
  | .error reason => failure outcome.frame reason
  | .ok .normal =>
      if resultType == .void then closeResult outcome.frame (.ok none)
      else failure outcome.frame .missingReturn
  | .ok .returnedVoid =>
      if resultType == .void then closeResult outcome.frame (.ok none)
      else failure outcome.frame .returnTypeMismatch
  | .ok .break_ => failure outcome.frame .breakOutsideLoop
  | .ok .continue_ => failure outcome.frame .continueOutsideLoop
  | .ok (.goto_ label) => failure outcome.frame (.gotoOutsideFunction label)
  | .ok (.failed result) => success outcome.frame (liftIntegralResult result)
  | .ok (.returned result) =>
      if resultType == .void then failure outcome.frame .returnTypeMismatch
      else closeResult outcome.frame (liftIntegralResult result)

/-- Successful `none` denotes a void result, never an invented integral value. -/
def evaluateCallableObjectResultInFrame (fuel : Nat) (callable : CallableObjectFrame) :
    Outcome (IntegralResult (Option IntegralValue)) :=
  closeCallable callable.function.signature.result
    (evalStatement fuel callable.profile callable.frame callable.function.body)

private def integralOnly (outcome : Outcome (IntegralResult (Option IntegralValue))) :
    Outcome (IntegralResult IntegralValue) :=
  match outcome.result with
  | .error reason => failure outcome.frame reason
  | .ok (.ok (some value)) => success outcome.frame (.ok value)
  | .ok (.ok none) => failure outcome.frame .voidResultRequiresResultAPI
  | .ok (.invalid reason) => success outcome.frame (.invalid reason)
  | .ok (.undefined reason) => success outcome.frame (.undefined reason)
  | .ok (.unsupported reason) => success outcome.frame (.unsupported reason)

def evaluateCallableObjectInFrame (fuel : Nat) (callable : CallableObjectFrame) :
    Outcome (IntegralResult IntegralValue) :=
  match fuel with
  | 0 => frameFailure callable.frame .fuelExhausted
  | _ + 1 =>
      if callable.function.signature.result == .void then
        failure callable.frame .voidResultRequiresResultAPI
      else integralOnly (evaluateCallableObjectResultInFrame fuel callable)

private def mapStartError : CallableFrameError → CallableObjectEvaluationError
  | .invalidProfile => .invalidProfile
  | .arityMismatch => .arityMismatch
  | .argumentInvalid reason => .invalidArgument reason
  | .argumentUndefined reason => .undefinedArgument reason
  | .argumentUnsupported reason => .unsupportedArgument reason
  | .argumentTypeMismatch declaration => .argumentTypeMismatch declaration
  | .object reason => .frameError reason

def evaluateCallableObject (fuel : Nat) (profile : TargetProfile)
    (function : CallableFunction) (arguments : List IntegralValue) :
    Except CallableObjectEvaluationError (IntegralResult IntegralValue) := do
  if function.signature.result == .void then throw .voidResultRequiresResultAPI
  let callable ← (CallableObjectFrame.start profile function arguments).mapError mapStartError
  let result := evaluateCallableObjectInFrame fuel callable
  result.result

/-- Execute an already-selected body with evaluated arguments in a caller's
store. Return the resulting store even on admission/setup/execution failure. -/
def evaluateCallableObjectInStore (fuel : Nat) (store : IntegralObjectStore)
    (function : CallableFunction) (arguments : List CallableArgument) :
    Outcome (IntegralResult IntegralValue) :=
  if function.signature.result == .void then
    failure {store, scopes := [], staticBindings := [], threadBindings := []}
      .voidResultRequiresResultAPI
  else
    let started := CallableObjectFrame.startInStore store function arguments
    match started.result with
    | .error reason => failure started.frame (mapStartError reason)
    | .ok callable => evaluateCallableObjectInFrame fuel callable

/-- Execute integral or void results with the same fresh parameter scope. -/
def evaluateCallableObjectResult (fuel : Nat) (profile : TargetProfile)
    (function : CallableFunction) (arguments : List IntegralValue) :
    Except CallableObjectEvaluationError (IntegralResult (Option IntegralValue)) := do
  let callable ← (CallableObjectFrame.start profile function arguments).mapError mapStartError
  (evaluateCallableObjectResultInFrame fuel callable).result

/-- Execute with caller-owned objects; retain the store on every failure. -/
def evaluateCallableObjectResultInStore (fuel : Nat) (store : IntegralObjectStore)
    (function : CallableFunction) (arguments : List CallableArgument) :
    Outcome (IntegralResult (Option IntegralValue)) :=
  let started := CallableObjectFrame.startInStore store function arguments
  match started.result with
  | .error reason => failure started.frame (mapStartError reason)
  | .ok callable => evaluateCallableObjectResultInFrame fuel callable

/-- At positive fuel, reaching the closing brace of a void function has exactly
    the same result and cleanup as a bare return, for every callee frame. -/
theorem void_fallthrough_eq_return (fuel : Nat) (callable : CallableObjectFrame)
    (h : callable.function.signature.result = .void) :
    evaluateCallableObjectResultInFrame (fuel + 1)
      {callable with function := {callable.function with body := .skip}} =
    evaluateCallableObjectResultInFrame (fuel + 1)
      {callable with function := {callable.function with body := .returnVoid}} := by
  simp only [evaluateCallableObjectResultInFrame, evalStatement, success, closeCallable, h]
  rfl

/-- A return publishes the expression result when the frame closes cleanly. -/
theorem evaluateCallableObject_return_noParameters (fuel : Nat) (profile : TargetProfile) (function : CallableFunction)
    (callable : CallableObjectFrame) (expression : TypedCallableExpression)
    (result : IntegralResult IntegralValue)
    (hresult : (function.signature.result == .void) = false)
    (hstart : CallableObjectFrame.start profile function [] = .ok callable)
    (hfunction : callable.function = function) (hprofile : callable.profile = profile)
    (hbody : function.body = .return_ expression)
    (hexpr : evaluateCallableObjectExpression fuel profile callable.frame expression =
      {frame := callable.frame, result := .ok result})
    (hclose : callable.frame.leaveFrame.result = .ok ()) :
    evaluateCallableObject (fuel + 1) profile function [] = .ok result := by
  simp only [evaluateCallableObjectExpression] at hexpr
  cases result <;>
    simp [evaluateCallableObject, hresult, hstart, evaluateCallableObjectInFrame,
      evaluateCallableObjectResultInFrame, hfunction, hprofile, hbody, evalStatement, hexpr,
      closeCallable, closeResult, hclose, liftIntegralResult, integralOnly, success,
      Except.mapError, Except.bind, Bind.bind]
/-- A block return leaves its empty nested scope and closes the callable frame. -/
theorem evaluateCallableObject_blockReturn_noParameters (fuel : Nat) (profile : TargetProfile) (function : CallableFunction)
    (callable : CallableObjectFrame) (expression : TypedCallableExpression)
    (result : IntegralResult IntegralValue)
    (hresult : (function.signature.result == .void) = false)
    (hstart : CallableObjectFrame.start profile function [] = .ok callable)
    (hfunction : callable.function = function) (hprofile : callable.profile = profile)
    (hbody : function.body = .block (.return_ expression))
    (hexpr : evaluateCallableObjectExpression fuel profile callable.frame.enterScope.frame expression =
      {frame := callable.frame.enterScope.frame, result := .ok result})
    (hclose : callable.frame.leaveFrame.result = .ok ()) :
    evaluateCallableObject (fuel + 2) profile function [] = .ok result := by
  simp only [evaluateCallableObjectExpression] at hexpr
  have hent : callable.frame.enterScope.result = .ok () := rfl
  have hexit := IntegralObjectFrame.enterScope_exitScope callable.frame
  cases result <;>
    simp [evaluateCallableObject, hresult, hstart, evaluateCallableObjectInFrame,
      evaluateCallableObjectResultInFrame, hfunction, hprofile, hbody, evalStatement, hexpr,
      hent, hexit, closeCallable, closeResult, hclose, liftIntegralResult, integralOnly, success,
      Except.mapError, Except.bind, Bind.bind]
end CallableObjectEvaluation

end LeanModels.Cpp
