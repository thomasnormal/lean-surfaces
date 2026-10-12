import LeanModels.Cpp.IntegralObjectExpressions

namespace LeanModels.Cpp

inductive IntegralObjectStatement where
  | expression (expression : IntegralObjectExpression)
  | initialize (object : ObjectId) (sourceType : CppTypeEvidence)
      (expression : IntegralObjectExpression)
  | defaultInitialize (object : ObjectId)
  | assign (access : IntegralObjectRef) (sourceType : CppTypeEvidence)
      (expression : IntegralObjectExpression)
  | conditional (condition : IntegralObjectExpression)
      (whenTrue whenFalse : IntegralObjectStatement)
  | whileLoop (condition : IntegralObjectExpression) (body : IntegralObjectStatement)
  | forLoop (initializer : IntegralObjectStatement) (condition : IntegralObjectExpression)
      (step body : IntegralObjectStatement)
  | break_
  | continue_
  | sequence (first second : IntegralObjectStatement)
  deriving Repr, BEq, Inhabited

inductive IntegralObjectStatementError where
  | fuelExhausted
  | object (reason : IntegralObjectError)
  | invalid (reason : InvalidIntegral)
  | undefined (reason : IntegralUB)
  | unsupported (reason : IntegralUnsupported)
  | breakOutsideLoop
  | continueOutsideLoop
  deriving Repr, BEq, Inhabited

private inductive Execution where
  | normal (store : IntegralObjectStore)
  | break_ (store : IntegralObjectStore)
  | continue_ (store : IntegralObjectStore)

private def mapExpressionError : IntegralObjectExpressionError → IntegralObjectStatementError
  | .fuelExhausted => .fuelExhausted
  | .object reason => .object reason

private def requireResult : IntegralResult IntegralValue →
    Except IntegralObjectStatementError Unit
  | .ok _ => .ok ()
  | .invalid reason => .error (.invalid reason)
  | .undefined reason => .error (.undefined reason)
  | .unsupported reason => .error (.unsupported reason)

mutual
  private def executeStep (fuel : Nat) (store : IntegralObjectStore)
      (statement : IntegralObjectStatement) :
      Except IntegralObjectStatementError Execution :=
    match fuel with
    | 0 => .error .fuelExhausted
    | fuel + 1 =>
        match statement with
        | .expression expression => do
            let result ← (evaluateIntegralObjectExpression fuel store expression).mapError
              mapExpressionError
            let _ ← requireResult result
            pure (.normal store)
        | .initialize object sourceType expression => do
            let result ← (evaluateIntegralObjectExpression fuel store expression).mapError
              mapExpressionError
            match result with
            | .ok value =>
                (store.initializeConverted object sourceType value).mapError (.object)
                  |>.map Execution.normal
            | .invalid reason => throw (.invalid reason)
            | .undefined reason => throw (.undefined reason)
            | .unsupported reason => throw (.unsupported reason)
        | .defaultInitialize object =>
            (store.defaultInitialize object).mapError (.object)
              |>.map Execution.normal
        | .assign access sourceType expression => do
            let result ← (evaluateIntegralObjectExpression fuel store expression).mapError
              mapExpressionError
            match result with
            | .ok value =>
                (store.assignConverted access sourceType value).mapError (.object)
                  |>.map Execution.normal
            | .invalid reason => throw (.invalid reason)
            | .undefined reason => throw (.undefined reason)
            | .unsupported reason => throw (.unsupported reason)
        | .conditional condition whenTrue whenFalse => do
            let result ← (evaluateIntegralObjectExpression fuel store condition).mapError
              mapExpressionError
            match result with
            | .ok value =>
                if value.value == 0 then executeStep fuel store whenFalse
                else executeStep fuel store whenTrue
            | .invalid reason => throw (.invalid reason)
            | .undefined reason => throw (.undefined reason)
            | .unsupported reason => throw (.unsupported reason)
        | .whileLoop condition body => do
            let result ← (evaluateIntegralObjectExpression fuel store condition).mapError
              mapExpressionError
            match result with
            | .ok value =>
                if value.value == 0 then pure (.normal store)
                else
                  let result ← executeStep fuel store body
                  match result with
                  | .normal store | .continue_ store =>
                      executeStep fuel store (.whileLoop condition body)
                  | .break_ store => pure (.normal store)
            | .invalid reason => throw (.invalid reason)
            | .undefined reason => throw (.undefined reason)
            | .unsupported reason => throw (.unsupported reason)
        | .forLoop initializer condition step body => do
            let result ← executeStep fuel store initializer
            match result with
            | .normal store => executeForLoop fuel store condition step body
            | .break_ store => pure (.break_ store)
            | .continue_ store => pure (.continue_ store)
        | .break_ => pure (.break_ store)
        | .continue_ => pure (.continue_ store)
        | .sequence first second => do
            let result ← executeStep fuel store first
            match result with
            | .normal store => executeStep fuel store second
            | .break_ store => pure (.break_ store)
            | .continue_ store => pure (.continue_ store)

  private def executeForLoop (fuel : Nat) (store : IntegralObjectStore)
      (condition : IntegralObjectExpression) (step body : IntegralObjectStatement) :
      Except IntegralObjectStatementError Execution :=
    match fuel with
    | 0 => .error .fuelExhausted
    | fuel + 1 => do
        let result ← (evaluateIntegralObjectExpression fuel store condition).mapError
          mapExpressionError
        match result with
        | .ok value =>
            if value.value == 0 then pure (.normal store)
            else
              let bodyResult ← executeStep fuel store body
              match bodyResult with
              | .break_ store => pure (.normal store)
              | .normal store | .continue_ store =>
                  let stepResult ← executeStep fuel store step
                  match stepResult with
                  | .normal store | .continue_ store =>
                      executeForLoop fuel store condition step body
                  | .break_ store => pure (.break_ store)
        | .invalid reason => throw (.invalid reason)
        | .undefined reason => throw (.undefined reason)
        | .unsupported reason => throw (.unsupported reason)
end

def executeIntegralObjectStatement (fuel : Nat) (store : IntegralObjectStore)
    (statement : IntegralObjectStatement) :
    Except IntegralObjectStatementError IntegralObjectStore :=
  match executeStep fuel store statement with
  | .ok (.normal store) => .ok store
  | .ok (.break_ _) => .error .breakOutsideLoop
  | .ok (.continue_ _) => .error .continueOutsideLoop
  | .error reason => .error reason

end LeanModels.Cpp
