import LeanModels.Cpp.CallableFrame

namespace LeanModels.Cpp

inductive CallableObjectEvaluationError where
  | invalidProfile
  | arityMismatch
  | invalidArgument (reason : InvalidIntegral)
  | undefinedArgument (reason : IntegralUB)
  | unsupportedArgument (reason : IntegralUnsupported)
  | argumentTypeMismatch (declaration : FrontendHandle)
  | unsupportedOperator (operator : String)
  | missingReturn
  | breakOutsideLoop
  | continueOutsideLoop
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

private def builtinIntegralType : CppTypeEvidence → Option CppIntType
  | .builtin type => some type
  | .qualified _ _ base => builtinIntegralType base
  | _ => none

private def formatFor (profile : TargetProfile) (type : CppTypeEvidence) :
    Option IntegralFormat :=
  builtinIntegralType type |>.bind fun integer =>
    (profile.format integer).toOption

private def mapIntegralResult (result : IntegralResult IntegralValue)
    (convert : IntegralValue → IntegralResult IntegralValue) :
    IntegralResult IntegralValue :=
  match result with
  | .ok value => convert value
  | .invalid reason => .invalid reason
  | .undefined reason => .undefined reason
  | .unsupported reason => .unsupported reason

private def mapOutcome (outcome : Outcome (IntegralResult IntegralValue))
    (convert : IntegralValue → IntegralResult IntegralValue) :
    Outcome (IntegralResult IntegralValue) :=
  match outcome.result with
  | .error reason => failure outcome.frame reason
  | .ok result => success outcome.frame (mapIntegralResult result convert)

private def convertTo (profile : TargetProfile) (type : CppTypeEvidence)
    (value : IntegralValue) : IntegralResult IntegralValue :=
  match formatFor profile type with
  | some format => integralConvert format value
  | none => .unsupported .unresolvedArithmeticConversions

private def operator? : String → Option IntegralBinary
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

private def unaryOperator? : String → Option IntegralUnary
  | "+" => some .plus
  | "-" => some .negate
  | "~" => some .complement
  | "!" => some .logicalNot
  | _ => none

private def literalValue (profile : TargetProfile) (typed : TypedCallableExpression) (value : Nat) :
    Option IntegralValue :=
  (formatFor profile typed.sourceType).map fun format =>
    {format, value := Int.ofNat value}

private inductive Execution where
  | normal
  | returned (result : IntegralResult IntegralValue)
  | failed (result : IntegralResult IntegralValue)
  | break_
  | continue_
  deriving Inhabited

private def compoundOperator? : String → Option IntegralBinary
  | "+=" => some .add
  | "-=" => some .subtract
  | "*=" => some .multiply
  | "/=" => some .divide
  | "%=" => some .remainder
  | "&=" => some .bitAnd
  | "|=" => some .bitOr
  | "^=" => some .bitXor
  | "<<=" => some .shiftLeft
  | ">>=" => some .shiftRight
  | _ => none

private def switchCaseSuffix (value : Int) : List CallableSwitchClause →
    Option (List CallableSwitchClause)
  | [] => none
  | clause :: rest =>
      match clause.label with
      | some label => if label == value then some (clause :: rest) else switchCaseSuffix value rest
      | none => switchCaseSuffix value rest

private def switchDefaultSuffix : List CallableSwitchClause →
    Option (List CallableSwitchClause)
  | [] => none
  | clause :: rest =>
      match clause.label with
      | some _ => switchDefaultSuffix rest
      | none => some (clause :: rest)

private def finishResult (frame : IntegralObjectFrame)
    (result : IntegralResult IntegralValue) : Outcome Execution :=
  match result with
  | .ok _ => success frame .normal
  | _ => success frame (.failed result)

mutual
  private partial def evalIncrement (fuel : Nat) (profile : TargetProfile)
      (frame : IntegralObjectFrame) (typed : TypedCallableExpression)
      (operator : String) (isPostfix : Bool) (declaration : FrontendHandle) :
      Outcome (IntegralResult IntegralValue) :=
    let current := evalExpression fuel profile frame
      {typed with expression := .parameter declaration}
    match current.result with
    | .error reason => failure current.frame reason
    | .ok result =>
        match result with
        | .ok old =>
            let operation := if operator == "++" then IntegralBinary.add
              else IntegralBinary.subtract
            let next := integralBinary operation old ⟨old.format, 1⟩
            match next with
            | .ok value =>
                match current.frame.lookup declaration with
                | .error reason => frameFailure current.frame reason
                | .ok binding =>
                    let assigned := current.frame.assignValue declaration binding.type value
                    match assigned.result with
                    | .error reason => frameFailure assigned.frame reason
                    | .ok _ =>
                        success assigned.frame (convertTo profile typed.type
                          (if isPostfix then old else value))
            | result =>
                success current.frame (mapIntegralResult result (convertTo profile typed.type))
        | result =>
            success current.frame (mapIntegralResult result (convertTo profile typed.type))

  private partial def evalExpression (fuel : Nat) (profile : TargetProfile)
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
        | .parameter declaration =>
            let read := frame.evaluate fuel (.read declaration)
            match read.result with
            | .error reason => frameFailure read.frame reason
            | .ok result => success read.frame (mapIntegralResult result (convertTo profile typed.type))
        | .increment operator isPostfix declaration =>
            evalIncrement fuel profile frame typed operator isPostfix declaration
        | .convert operand =>
            mapOutcome (evalExpression fuel profile frame operand)
              (convertTo profile typed.type)
        | .unary operator operand =>
            let evaluated := evalExpression fuel profile frame operand
            match evaluated.result with
            | .error reason => failure evaluated.frame reason
            | .ok result =>
                match unaryOperator? operator with
                | none => success evaluated.frame (.unsupported .unresolvedArithmeticConversions)
                | some operation =>
                    success evaluated.frame (mapIntegralResult result fun value =>
                      mapIntegralResult (integralUnary operation value)
                        (convertTo profile typed.type))
        | .binary operator left right =>
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
                      match operator? operator with
                      | none => success rightResult.frame
                          (.unsupported .unresolvedArithmeticConversions)
                      | some operation =>
                          let combined := match leftValue, rightValue with
                            | .ok left, .ok right => integralBinary operation left right
                            | .invalid reason, _ | _, .invalid reason => .invalid reason
                            | .undefined reason, _ | _, .undefined reason => .undefined reason
                            | .unsupported reason, _ | _, .unsupported reason =>
                                .unsupported reason
                          success rightResult.frame
                            (mapIntegralResult combined (convertTo profile typed.type))
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
            let leftResult := evalExpression fuel profile frame left
            match leftResult.result with
            | .error reason => failure leftResult.frame reason
            | .ok (.ok value) =>
                let leftTrue := value.value != 0
                if (operator == "&&" && !leftTrue) || (operator == "||" && leftTrue) then
                  success leftResult.frame (.ok (integralBoolean (if operator == "&&" then false else true)))
                else
                  let rightResult := evalExpression fuel profile leftResult.frame right
                  match rightResult.result with
                  | .error reason => failure rightResult.frame reason
                  | .ok (.ok rightValue) =>
                      success rightResult.frame (.ok (integralBoolean (rightValue.value != 0)))
                  | .ok result => success rightResult.frame result
            | .ok result => success leftResult.frame result

  private partial def evalStatement (fuel : Nat) (profile : TargetProfile)
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
            let evaluated := evalExpression fuel profile frame expression
            match evaluated.result with
            | .error reason => failure evaluated.frame reason
            | .ok (.ok rightValue) =>
                match compoundOperator? operator with
                | none => failure evaluated.frame (.unsupportedOperator operator)
                | some operation =>
                  match evaluated.frame.lookup declaration with
                  | .error reason => frameFailure evaluated.frame reason
                  | .ok binding =>
                      match evaluated.frame.evaluate 1 (.read declaration) with
                      | read =>
                          match read.result with
                          | .error reason => frameFailure read.frame reason
                          | .ok (.ok current) =>
                              let combined := integralBinary operation current rightValue
                              match combined with
                              | .ok value =>
                                  let assigned := read.frame.assignValue declaration binding.type value
                                  match assigned.result with
                                  | .error reason => frameFailure assigned.frame reason
                                  | .ok _ => success assigned.frame .normal
                              | result => success read.frame (.failed result)
                          | .ok result => success read.frame (.failed result)
            | .ok result => success evaluated.frame (.failed result)
        | .return_ expression =>
            let evaluated := evalExpression fuel profile frame expression
            match evaluated.result with
            | .error reason => failure evaluated.frame reason
            | .ok (.ok value) => success evaluated.frame (.returned (.ok value))
            | .ok result => success evaluated.frame (.failed result)
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
                let selected := (switchCaseSuffix value.value clauses).orElse
                  (fun _ => switchDefaultSuffix clauses) |>.getD []
                evalSwitch fuel profile evaluated.frame selected
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
                | .ok execution => success initial.frame execution
        | .break_ => success frame .break_
        | .continue_ => success frame .continue_
        | .sequence first second =>
            let firstResult := evalStatement fuel profile frame first
            match firstResult.result with
            | .error reason => failure firstResult.frame reason
            | .ok .normal => evalStatement fuel profile firstResult.frame second
            | .ok execution => success firstResult.frame execution

  private partial def evalWhile (fuel : Nat) (profile : TargetProfile)
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

  private partial def evalDoWhile (fuel : Nat) (profile : TargetProfile)
      (frame : IntegralObjectFrame) (body : CallableStatement)
      (condition : TypedCallableExpression) : Outcome Execution :=
    match fuel with
    | 0 => frameFailure frame .fuelExhausted
    | fuel + 1 =>
        let bodyResult := evalStatement fuel profile frame body
        match bodyResult.result with
        | .error reason => failure bodyResult.frame reason
        | .ok .break_ => success bodyResult.frame .normal
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

  private partial def evalFor (fuel : Nat) (profile : TargetProfile)
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

  private partial def evalSwitch (fuel : Nat) (profile : TargetProfile)
      (frame : IntegralObjectFrame) :
      List CallableSwitchClause → Outcome Execution
    | [] => success frame .normal
    | clause :: rest =>
        let current := evalStatement fuel profile frame clause.body
        match current.result with
        | .error reason => failure current.frame reason
        | .ok .normal => evalSwitch fuel profile current.frame rest
        | .ok .break_ => success current.frame .normal
        | .ok execution => success current.frame execution
end

private def closeCallable (outcome : Outcome Execution) :
    Outcome (IntegralResult IntegralValue) :=
  match outcome.result with
  | .error reason => failure outcome.frame reason
  | .ok .normal => failure outcome.frame .missingReturn
  | .ok .break_ => failure outcome.frame .breakOutsideLoop
  | .ok .continue_ => failure outcome.frame .continueOutsideLoop
  | .ok (.failed result) => success outcome.frame result
  | .ok (.returned result) =>
      let closed := outcome.frame.leaveFrame
      match closed.result with
      | .error reason => frameFailure closed.frame reason
      | .ok _ => success closed.frame result

def evaluateCallableObjectInFrame (fuel : Nat) (callable : CallableObjectFrame) :
    Outcome (IntegralResult IntegralValue) :=
  closeCallable (evalStatement fuel callable.profile callable.frame callable.function.body)

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
  let callable ← (CallableObjectFrame.start profile function arguments).mapError mapStartError
  let result := evaluateCallableObjectInFrame fuel callable
  result.result

end CallableObjectEvaluation

end LeanModels.Cpp
