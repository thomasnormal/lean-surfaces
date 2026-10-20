import LeanModels.Cpp.IntegralObjects

namespace LeanModels.Cpp

inductive FrameBindingRole where
  | parameter
  | local
  deriving Repr, BEq, Inhabited

structure FrameBinding where
  declaration : FrontendHandle
  object : ObjectId
  type : CppTypeEvidence
  role : FrameBindingRole
  deriving Repr, BEq, Inhabited

structure FrameScope where
  bindings : List FrameBinding
  deriving Repr, BEq, Inhabited

structure IntegralObjectFrame where
  store : IntegralObjectStore
  /-- The head is the innermost lexical scope. -/
  scopes : List FrameScope
  deriving Repr, BEq, Inhabited

inductive FrameError where
  | invalidProfile
  | object (reason : IntegralObjectError)
  | fuelExhausted
  | missingBinding (declaration : FrontendHandle)
  | duplicateBinding (declaration : FrontendHandle)
  | noActiveScope
  | noScopeToExit
  | unsupportedDuration (duration : StorageDuration)
  | invalid (reason : InvalidIntegral)
  | undefined (reason : IntegralUB)
  | unsupported (reason : IntegralUnsupported)
  | breakOutsideLoop
  | continueOutsideLoop
  deriving Repr, BEq, Inhabited

structure FrameOutcome (α : Type) where
  /-- State is retained even when `result` is an error. -/
  frame : IntegralObjectFrame
  result : Except FrameError α
  deriving Inhabited

namespace IntegralObjectFrame

inductive Expression where
  | literal (value : IntegralValue)
  | read (declaration : FrontendHandle)
  | convert (destination : IntegralFormat) (operand : Expression)
  | unary (operation : IntegralUnary) (operand : Expression)
  | binary (operation : IntegralBinary) (left right : Expression)
  deriving Repr, BEq, Inhabited

inductive Statement where
  | skip
  | expression (expression : Expression)
  | declare (declaration : FrontendHandle) (type sourceType : CppTypeEvidence)
      (expression : Expression)
  | defaultDeclare (declaration : FrontendHandle) (type : CppTypeEvidence)
  | zeroDeclare (declaration : FrontendHandle) (type : CppTypeEvidence)
  | assign (declaration : FrontendHandle) (sourceType : CppTypeEvidence)
      (expression : Expression)
  | block (body : Statement)
  | conditional (condition : Expression) (whenTrue whenFalse : Statement)
  | whileLoop (condition : Expression) (body : Statement)
  | forLoop (initializer : Statement) (condition : Expression)
      (step body : Statement)
  | break_
  | continue_
  | return_ (expression : Expression)
  | sequence (first second : Statement)
  deriving Repr, BEq, Inhabited

private inductive Execution where
  | normal
  | returned (value : IntegralValue)
  | break_
  | continue_
  deriving Repr, BEq, Inhabited

def empty (profile : TargetProfile) : Except FrameError IntegralObjectFrame :=
  match IntegralObjectStore.empty profile with
  | .ok store => .ok {store, scopes := []}
  | .error .invalidProfile => .error .invalidProfile
  | .error reason => .error (.object reason)

private def success (frame : IntegralObjectFrame) (value : α) : FrameOutcome α :=
  {frame, result := .ok value}

private def failure (frame : IntegralObjectFrame) (reason : FrameError) : FrameOutcome α :=
  {frame, result := .error reason}

def scopeDepth (frame : IntegralObjectFrame) : Nat := frame.scopes.length

def enterScope (frame : IntegralObjectFrame) : FrameOutcome Unit :=
  success {frame with scopes := {bindings := []} :: frame.scopes} ()

private def binding? (scopes : List FrameScope)
    (declaration : FrontendHandle) : Option FrameBinding :=
  match scopes with
  | [] => none
  | scope :: rest =>
      match scope.bindings.find? (fun binding => binding.declaration == declaration) with
      | some binding => some binding
      | none => binding? rest declaration

def lookup (frame : IntegralObjectFrame) (declaration : FrontendHandle) :
    Except FrameError FrameBinding :=
  match binding? frame.scopes declaration with
  | some binding => .ok binding
  | none => .error (.missingBinding declaration)

def bound (frame : IntegralObjectFrame) (declaration : FrontendHandle) : Bool :=
  (binding? frame.scopes declaration).isSome

private def addBinding (frame : IntegralObjectFrame) (binding : FrameBinding) :
    FrameOutcome ObjectId :=
  let alreadyBound := (binding? frame.scopes binding.declaration).isSome
  if alreadyBound then
    failure frame (.duplicateBinding binding.declaration)
  else
    match frame.scopes with
    | [] => failure frame .noActiveScope
    | scope :: rest =>
        success {frame with scopes := {scope with bindings := binding :: scope.bindings} :: rest}
          binding.object

private def reserve (frame : IntegralObjectFrame) (declaration : FrontendHandle)
    (type : CppTypeEvidence) (role : FrameBindingRole) : FrameOutcome ObjectId :=
  let binding : FrameBinding := {declaration, object := 0, type, role}
  let alreadyBound := frame.bound declaration
  if alreadyBound then
    failure frame (.duplicateBinding declaration)
  else match frame.scopes with
    | [] => failure frame .noActiveScope
    | _ =>
        match frame.store.allocate .automatic type with
        | .error reason => failure frame (.object reason)
        | .ok (store, object) =>
            let binding := {binding with object}
            addBinding {frame with store} binding

private def mapResult : IntegralResult IntegralValue → Except FrameError IntegralValue
  | .ok value => .ok value
  | .invalid reason => .error (.invalid reason)
  | .undefined reason => .error (.undefined reason)
  | .unsupported reason => .error (.unsupported reason)

private def propagate : IntegralResult IntegralValue →
    IntegralResult IntegralValue → IntegralResult IntegralValue
  | .invalid reason, _ | _, .invalid reason => .invalid reason
  | .undefined reason, _ | _, .undefined reason => .undefined reason
  | .unsupported reason, _ | _, .unsupported reason => .unsupported reason
  | .ok _, result => result

partial def evaluate (fuel : Nat) (frame : IntegralObjectFrame) (expression : Expression) :
      FrameOutcome (IntegralResult IntegralValue) :=
    match fuel with
    | 0 => failure frame .fuelExhausted
    | fuel + 1 =>
        match expression with
        | .literal value => success frame <| match value.invalid? with
            | some reason => .invalid reason
            | none => .ok value
        | .read declaration =>
            match frame.lookup declaration with
            | .error reason => failure frame reason
            | .ok binding =>
                match frame.store.borrow binding.object with
                | .error reason => failure frame (.object reason)
                | .ok access =>
                    match frame.store.read access with
                    | .ok value => success frame (.ok value)
                    | .error reason => failure frame (.object reason)
        | .convert destination operand =>
            let result := evaluate fuel frame operand
            match result.result with
            | .error reason => failure result.frame reason
            | .ok value => success result.frame <| match value with
                | .ok value => integralConvert destination value
                | .invalid reason => .invalid reason
                | .undefined reason => .undefined reason
                | .unsupported reason => .unsupported reason
        | .unary operation operand =>
            let result := evaluate fuel frame operand
            match result.result with
            | .error reason => failure result.frame reason
            | .ok value => success result.frame <| match value with
                | .ok value => integralUnary operation value
                | .invalid reason => .invalid reason
                | .undefined reason => .undefined reason
                | .unsupported reason => .unsupported reason
        | .binary operation left right =>
            let leftResult := evaluate fuel frame left
            match leftResult.result with
            | .error reason => failure leftResult.frame reason
            | .ok leftValue =>
                let rightResult := evaluate fuel leftResult.frame right
                match rightResult.result with
                | .error reason => failure rightResult.frame reason
                | .ok rightValue =>
                    match leftValue, rightValue with
                    | .ok leftValue, .ok rightValue =>
                        success rightResult.frame (integralBinary operation leftValue rightValue)
                    | leftValue, rightValue =>
                        success rightResult.frame (propagate leftValue rightValue)
def read (frame : IntegralObjectFrame) (declaration : FrontendHandle) :
    FrameOutcome IntegralValue :=
  let result := evaluate 1 frame (.read declaration)
  match result.result with
  | .error reason => failure result.frame reason
  | .ok value =>
      match mapResult value with
      | .ok value => success result.frame value
      | .error reason => failure result.frame reason

private def reserveInitialized (frame : IntegralObjectFrame)
    (declaration : FrontendHandle) (type : CppTypeEvidence)
    (role : FrameBindingRole) (value : IntegralValue) : FrameOutcome ObjectId :=
  let reserved := reserve frame declaration type role
  match reserved.result with
  | .error reason => failure reserved.frame reason
  | .ok object =>
      match reserved.frame.store.initializeValue object value with
      | .ok store => success {reserved.frame with store} object
      | .error reason => failure reserved.frame (.object reason)

def declareParameter (frame : IntegralObjectFrame) (declaration : FrontendHandle)
    (type : CppTypeEvidence) (value : IntegralValue) : FrameOutcome ObjectId :=
  reserveInitialized frame declaration type .parameter value

def declareLocalInitialized (fuel : Nat) (frame : IntegralObjectFrame)
    (declaration : FrontendHandle) (type : CppTypeEvidence)
    (sourceType : CppTypeEvidence) (expression : Expression) : FrameOutcome ObjectId :=
  let reserved := reserve frame declaration type .local
  match reserved.result with
  | .error reason => failure reserved.frame reason
  | .ok object =>
      let evaluated := evaluate fuel reserved.frame expression
      match evaluated.result with
      | .error reason => failure evaluated.frame reason
      | .ok result =>
          match result with
          | .ok value =>
              match evaluated.frame.store.initializeConverted object sourceType value with
              | .ok store => success {evaluated.frame with store} object
              | .error reason => failure evaluated.frame (.object reason)
          | .invalid reason => failure evaluated.frame (.invalid reason)
          | .undefined reason => failure evaluated.frame (.undefined reason)
          | .unsupported reason => failure evaluated.frame (.unsupported reason)

def declareLocalDefault (frame : IntegralObjectFrame) (declaration : FrontendHandle)
    (type : CppTypeEvidence) : FrameOutcome ObjectId :=
  let reserved := reserve frame declaration type .local
  match reserved.result with
  | .error reason => failure reserved.frame reason
  | .ok object =>
      match reserved.frame.store.defaultInitialize object with
      | .ok store => success {reserved.frame with store} object
      | .error reason => failure reserved.frame (.object reason)

def declareLocalZero (frame : IntegralObjectFrame) (declaration : FrontendHandle)
    (type : CppTypeEvidence) : FrameOutcome ObjectId :=
  declareLocalInitialized 1 frame declaration type (.builtin .int) (.literal ⟨.signed 32, 0⟩)

def assignValue (frame : IntegralObjectFrame) (declaration : FrontendHandle)
    (sourceType : CppTypeEvidence) (value : IntegralValue) : FrameOutcome Unit :=
  match frame.lookup declaration with
  | .error reason => failure frame reason
  | .ok binding =>
      match frame.store.borrow binding.object with
      | .error reason => failure frame (.object reason)
      | .ok access =>
          match frame.store.assignConverted access sourceType value with
          | .ok store => success {frame with store} ()
          | .error reason => failure frame (.object reason)

def assign (fuel : Nat) (frame : IntegralObjectFrame) (declaration : FrontendHandle)
    (sourceType : CppTypeEvidence) (expression : Expression) : FrameOutcome Unit :=
  let evaluated := evaluate fuel frame expression
  match evaluated.result with
  | .error reason => failure evaluated.frame reason
  | .ok result =>
      match result with
      | .ok value => assignValue evaluated.frame declaration sourceType value
      | .invalid reason => failure evaluated.frame (.invalid reason)
      | .undefined reason => failure evaluated.frame (.undefined reason)
      | .unsupported reason => failure evaluated.frame (.unsupported reason)

private def endBindings (frame : IntegralObjectFrame) : List FrameBinding →
    FrameOutcome Unit
  | [] => success frame ()
  | binding :: rest =>
      match frame.store.endLifetime binding.object with
      | .error reason => failure frame (.object reason)
      | .ok store => endBindings {frame with store} rest

def exitScope (frame : IntegralObjectFrame) : FrameOutcome Unit :=
  match frame.scopes with
  | [] => failure frame .noScopeToExit
  | scope :: rest =>
      let ended := endBindings frame scope.bindings
      match ended.result with
      | .error reason => failure ended.frame reason
      | .ok _ => success {ended.frame with scopes := rest} ()

partial def leaveFrame (frame : IntegralObjectFrame) : FrameOutcome Unit :=
  match frame.scopes with
  | [] => success frame ()
  | _ =>
      let exited := exitScope frame
      match exited.result with
      | .error reason => failure exited.frame reason
      | .ok _ => leaveFrame exited.frame

def returnValue (fuel : Nat) (frame : IntegralObjectFrame)
    (expression : Expression) : FrameOutcome IntegralValue :=
  let evaluated := evaluate fuel frame expression
  match evaluated.result with
  | .error reason => failure evaluated.frame reason
  | .ok result =>
      match result with
      | .ok value =>
          let closed := leaveFrame evaluated.frame
          match closed.result with
          | .ok _ => success closed.frame value
          | .error reason => failure closed.frame reason
      | .invalid reason => failure evaluated.frame (.invalid reason)
      | .undefined reason => failure evaluated.frame (.undefined reason)
      | .unsupported reason => failure evaluated.frame (.unsupported reason)

private def requireExpressionResult (frame : IntegralObjectFrame)
    (result : IntegralResult IntegralValue) : FrameOutcome IntegralValue :=
  match result with
  | .ok value => success frame value
  | .invalid reason => failure frame (.invalid reason)
  | .undefined reason => failure frame (.undefined reason)
  | .unsupported reason => failure frame (.unsupported reason)

private def finishScope (result : FrameOutcome Execution) : FrameOutcome Execution :=
  match result.result with
  | .error reason => failure result.frame reason
  | .ok execution =>
      let exited := result.frame.exitScope
      match exited.result with
      | .ok _ => success exited.frame execution
      | .error reason => failure exited.frame reason

mutual
  partial def executeStep (fuel : Nat) (frame : IntegralObjectFrame)
      (statement : Statement) : FrameOutcome Execution :=
    match fuel with
    | 0 => failure frame .fuelExhausted
    | fuel + 1 =>
        match statement with
        | .skip => success frame .normal
        | .expression expression =>
            let evaluated := evaluate fuel frame expression
            match evaluated.result with
            | .error reason => failure evaluated.frame reason
            | .ok result =>
                let required := requireExpressionResult evaluated.frame result
                match required.result with
                | .ok _ => success required.frame .normal
                | .error reason => failure required.frame reason
        | .declare declaration type sourceType expression =>
            let declared := declareLocalInitialized fuel frame declaration type sourceType expression
            match declared.result with
            | .ok _ => success declared.frame .normal
            | .error reason => failure declared.frame reason
        | .defaultDeclare declaration type =>
            let declared := declareLocalDefault frame declaration type
            match declared.result with
            | .ok _ => success declared.frame .normal
            | .error reason => failure declared.frame reason
        | .zeroDeclare declaration type =>
            let declared := declareLocalZero frame declaration type
            match declared.result with
            | .ok _ => success declared.frame .normal
            | .error reason => failure declared.frame reason
        | .assign declaration sourceType expression =>
            let assigned := assign fuel frame declaration sourceType expression
            match assigned.result with
            | .ok _ => success assigned.frame .normal
            | .error reason => failure assigned.frame reason
        | .block body =>
            let entered := frame.enterScope
            match entered.result with
            | .error reason => failure entered.frame reason
            | .ok _ =>
                let bodyResult := executeStep fuel entered.frame body
                finishScope bodyResult
        | .conditional condition whenTrue whenFalse =>
            let evaluated := evaluate fuel frame condition
            match evaluated.result with
            | .error reason => failure evaluated.frame reason
            | .ok result =>
                let required := requireExpressionResult evaluated.frame result
                match required.result with
                | .error reason => failure required.frame reason
                | .ok value =>
                    if value.value == 0 then executeStep fuel required.frame whenFalse
                    else executeStep fuel required.frame whenTrue
        | .whileLoop condition body => executeWhile fuel frame condition body
        | .forLoop initializer condition step body =>
            let entered := frame.enterScope
            match entered.result with
            | .error reason => failure entered.frame reason
            | .ok _ =>
                let initial := executeStep fuel entered.frame initializer
                match initial.result with
                | .error reason => failure initial.frame reason
                | .ok .normal =>
                    let looped := executeFor fuel initial.frame condition step body
                    finishScope looped
                | .ok _ => finishScope initial
        | .break_ => success frame .break_
        | .continue_ => success frame .continue_
        | .return_ expression =>
            let evaluated := evaluate fuel frame expression
            match evaluated.result with
            | .error reason => failure evaluated.frame reason
            | .ok result =>
                let required := requireExpressionResult evaluated.frame result
                match required.result with
                | .ok value => success required.frame (.returned value)
                | .error reason => failure required.frame reason
        | .sequence first second =>
            let firstResult := executeStep fuel frame first
            match firstResult.result with
            | .error reason => failure firstResult.frame reason
            | .ok .normal => executeStep fuel firstResult.frame second
            | .ok execution => success firstResult.frame execution

  partial def executeWhile (fuel : Nat) (frame : IntegralObjectFrame)
      (condition : Expression) (body : Statement) : FrameOutcome Execution :=
    match fuel with
    | 0 => failure frame .fuelExhausted
    | fuel + 1 =>
        let evaluated := evaluate fuel frame condition
        match evaluated.result with
        | .error reason => failure evaluated.frame reason
        | .ok result =>
            let required := requireExpressionResult evaluated.frame result
            match required.result with
            | .error reason => failure required.frame reason
            | .ok value =>
                if value.value == 0 then success required.frame .normal
                else
                    let bodyResult := executeStep fuel required.frame body
                    match bodyResult.result with
                    | .error reason => failure bodyResult.frame reason
                    | .ok .break_ => success bodyResult.frame .normal
                    | .ok .normal | .ok .continue_ =>
                        executeWhile fuel bodyResult.frame condition body
                    | .ok returned => success bodyResult.frame returned

  partial def executeFor (fuel : Nat) (frame : IntegralObjectFrame)
      (condition : Expression) (step body : Statement) : FrameOutcome Execution :=
    match fuel with
    | 0 => failure frame .fuelExhausted
    | fuel + 1 =>
        let evaluated := evaluate fuel frame condition
        match evaluated.result with
        | .error reason => failure evaluated.frame reason
        | .ok result =>
            let required := requireExpressionResult evaluated.frame result
            match required.result with
            | .error reason => failure required.frame reason
            | .ok value =>
                if value.value == 0 then success required.frame .normal
                else
                    let bodyResult := executeStep fuel required.frame body
                    match bodyResult.result with
                    | .error reason => failure bodyResult.frame reason
                    | .ok .break_ => success bodyResult.frame .normal
                    | .ok (.returned value) => success bodyResult.frame (.returned value)
                    | .ok .normal | .ok .continue_ =>
                        let stepResult := executeStep fuel bodyResult.frame step
                        match stepResult.result with
                        | .error reason => failure stepResult.frame reason
                        | .ok .normal | .ok .continue_ =>
                            executeFor fuel stepResult.frame condition step body
                        | .ok execution => success stepResult.frame execution
end

private def closeExecution (result : FrameOutcome Execution) :
    FrameOutcome (Option IntegralValue) :=
  let closeWithError (frame : IntegralObjectFrame) (reason : FrameError) :
      FrameOutcome (Option IntegralValue) :=
    let closed := leaveFrame frame
    match closed.result with
    | .ok _ => failure closed.frame reason
    | .error cleanup => failure closed.frame cleanup
  match result.result with
  | .error reason => failure result.frame reason
  | .ok .break_ => closeWithError result.frame .breakOutsideLoop
  | .ok .continue_ => closeWithError result.frame .continueOutsideLoop
  | .ok .normal =>
      let closed := leaveFrame result.frame
      match closed.result with
      | .ok _ => success closed.frame none
      | .error reason => failure closed.frame reason
  | .ok (.returned value) =>
      let closed := leaveFrame result.frame
      match closed.result with
      | .ok _ => success closed.frame (some value)
      | .error reason => failure closed.frame reason

def execute (fuel : Nat) (frame : IntegralObjectFrame)
    (statement : Statement) : FrameOutcome (Option IntegralValue) :=
  closeExecution (executeStep fuel frame statement)

/-- Execute one object statement while retaining the caller's active scopes.
This is the embedding boundary used by callable bodies: a declaration
statement must not close the parameter frame merely because its own fragment
has completed. -/
def executeOpen (fuel : Nat) (frame : IntegralObjectFrame)
    (statement : Statement) : FrameOutcome (Option IntegralValue) :=
  match executeStep fuel frame statement with
  | result =>
      match result.result with
      | .error reason => failure result.frame reason
      | .ok .normal => success result.frame none
      | .ok (.returned value) => success result.frame (some value)
      | .ok .break_ => failure result.frame .breakOutsideLoop
      | .ok .continue_ => failure result.frame .continueOutsideLoop

end IntegralObjectFrame

end LeanModels.Cpp
