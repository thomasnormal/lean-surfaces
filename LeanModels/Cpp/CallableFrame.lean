import LeanModels.Cpp.Callable
import LeanModels.Cpp.AutomaticDeclarations

namespace LeanModels.Cpp

open IntegralObjectFrame

inductive CallableFrameError where
  | invalidProfile
  | arityMismatch
  | argumentInvalid (reason : InvalidIntegral)
  | argumentUndefined (reason : IntegralUB)
  | argumentUnsupported (reason : IntegralUnsupported)
  | argumentTypeMismatch (declaration : FrontendHandle)
  | object (reason : FrameError)
  deriving Repr, BEq, Inhabited

structure CallableObjectFrame where
  profile : TargetProfile
  function : CallableFunction
  frame : IntegralObjectFrame
  deriving Repr, BEq, Inhabited

/-- Evaluated argument category: a prvalue, or an existing-object lvalue view.
The latter retains both object identity and the caller's const qualification. -/
inductive CallableArgument where
  | value (value : IntegralValue)
  | lvalue (access : IntegralObjectRef)
  deriving Repr, BEq, Inhabited

structure CallableStartOutcome (α : Type) where
  frame : IntegralObjectFrame
  result : Except CallableFrameError α
  deriving Inhabited

namespace CallableObjectFrame

private def success (frame : IntegralObjectFrame) (value : α) : FrameOutcome α :=
  {frame, result := .ok value}

private def failure (frame : IntegralObjectFrame) (reason : FrameError) :
    FrameOutcome α :=
  {frame, result := .error reason}

private def builtinIntegralType : CppTypeEvidence → Option CppIntType
  | .builtin type => some type
  | .qualified _ _ base => builtinIntegralType base
  | _ => none

private def formatFor (profile : TargetProfile) (type : CppTypeEvidence) :
    Except (CppTypeEvidence × CppIntType) IntegralFormat :=
  match builtinIntegralType type with
  | none => .error (type, .int)
  | some integer =>
      match profile.format integer with
      | .ok format => .ok format
      | .error _ => .error (type, integer)

private def convertArgument (profile : TargetProfile) (parameter : CallableParameter)
    (argument : IntegralValue) : Except CallableFrameError IntegralValue := do
  let destination ← match formatFor profile parameter.type with
    | .ok format => pure format
    | .error (type, _) => throw (.argumentTypeMismatch parameter.declaration)
  match argument.invalid? with
  | some reason => throw (.argumentInvalid reason)
  | none =>
      match integralConvert destination argument with
      | .ok value => pure value
      | .invalid reason => throw (.argumentInvalid reason)
      | .undefined reason => throw (.argumentUndefined reason)
      | .unsupported reason => throw (.argumentUnsupported reason)

private def convertArguments (profile : TargetProfile) (parameters : List CallableParameter)
    (arguments : List IntegralValue) : Except CallableFrameError (List IntegralValue) :=
  match parameters, arguments with
  | [], [] => .ok []
  | parameter :: parameters, argument :: arguments => do
      let value ← convertArgument profile parameter argument
      let rest ← convertArguments profile parameters arguments
      pure (value :: rest)
  | _, _ => .error .arityMismatch

private def initializeParameters (frame : IntegralObjectFrame)
    (parameters : List CallableParameter) (arguments : List IntegralValue) :
    FrameOutcome Unit :=
  match parameters, arguments with
  | [], [] => success frame ()
  | parameter :: parameters, argument :: arguments =>
      let declared := frame.declareParameter parameter.declaration parameter.type argument
      match declared.result with
      | .error reason => failure declared.frame reason
      | .ok _ => initializeParameters declared.frame parameters arguments
  | _, _ => failure frame .invalidProfile

/-- Start an object-backed callable frame with an outer parameter scope. -/
def start (profile : TargetProfile) (function : CallableFunction)
    (arguments : List IntegralValue) : Except CallableFrameError CallableObjectFrame := do
  unless profile.valid do throw .invalidProfile
  unless arguments.length == function.parameters.length do throw .arityMismatch
  let converted ← convertArguments profile function.parameters arguments
  let frame ← match IntegralObjectFrame.empty profile with
    | .ok frame => pure frame
    | .error reason => throw (CallableFrameError.object reason)
  let entered := frame.enterScope
  let entered ← match entered.result with
    | .ok _ => pure entered.frame
    | .error reason => throw (CallableFrameError.object reason)
  let initialized := initializeParameters entered function.parameters converted
  match initialized.result with
  | .ok _ => pure {profile, function, frame := initialized.frame}
  | .error reason => throw (CallableFrameError.object reason)

private def validateSuppliedIdentities (store : IntegralObjectStore) :
    List CallableArgument → Except CallableFrameError Unit
  | [] => .ok ()
  | argument :: rest => do
      match argument with
      | .value _ => pure ()
      | .lvalue access =>
          let _ ← (store.bindReference access access.type).mapError
            (fun reason => .object (.object reason))
          pure ()
      validateSuppliedIdentities store rest

private def initializeSupplied (frame : IntegralObjectFrame)
    (parameters : List CallableParameter) (arguments : List CallableArgument) :
    CallableStartOutcome Unit :=
  match parameters, arguments with
  | [], [] => {frame, result := .ok ()}
  | parameter :: parameters, argument :: arguments =>
      let initialized : CallableStartOutcome Unit :=
        match parameter.type with
        | .lvalueReference referent =>
            match argument with
            | .value _ => {frame, result := .error (.argumentTypeMismatch parameter.declaration)}
            | .lvalue access =>
                let bound := frame.bindReferenceParameter parameter.declaration referent access
                {frame := bound.frame, result := bound.result.map (fun _ => ()) |>.mapError .object}
        | _ =>
            let prepared : Except CallableFrameError IntegralValue := do
              let value ← match argument with
                | .value value => pure value
                | .lvalue access =>
                    (frame.store.read access).mapError (fun reason => .object (.object reason))
              convertArgument frame.store.profile parameter value
            match prepared with
            | .error reason => {frame, result := .error reason}
            | .ok value =>
                let declared := frame.declareParameter parameter.declaration parameter.type value
                {frame := declared.frame,
                 result := declared.result.map (fun _ => ()) |>.mapError .object}
      match initialized.result with
      | .error reason => {frame := initialized.frame, result := .error reason}
      | .ok _ => initializeSupplied initialized.frame parameters arguments
  | _, _ => {frame, result := .error .arityMismatch}

/-- Start fresh callee bindings over a shared store. No caller declaration
scope is imported. Every setup failure retains the initialized prefix. -/
def startInStore (store : IntegralObjectStore) (function : CallableFunction)
    (arguments : List CallableArgument) : CallableStartOutcome CallableObjectFrame :=
  let frame : IntegralObjectFrame := {
    store, scopes := [],
    staticBindings := store.staticBindings.map fun binding => {
      declaration := binding.declaration, object := binding.object,
      type := binding.type, role := .staticLocal},
    threadBindings := store.threadBindings.map fun binding => {
      declaration := binding.declaration, object := binding.object,
      type := binding.type, role := .threadLocal}}
  if !store.profile.valid then {frame, result := .error .invalidProfile}
  else if store.values.length != store.objects.objects.length then
    {frame, result := .error (.object (.object .incoherentValues))}
  else if arguments.length != function.parameters.length then
    {frame, result := .error .arityMismatch}
  else
    -- Validate against the entry store: an invalid argument ID must not become
    -- valid merely because an earlier value parameter allocates that ID.
    match validateSuppliedIdentities store arguments with
    | .error reason => {frame, result := .error reason}
    | .ok _ =>
        let initialized := initializeSupplied frame.enterScope.frame function.parameters arguments
        match initialized.result with
        | .error reason => {frame := initialized.frame, result := .error reason}
        | .ok _ => {frame := initialized.frame, result := .ok {
            profile := store.profile, function, frame := initialized.frame}}

/-- Execute a frontend-admitted declaration fragment in this callable frame. -/
def executeDeclStmt (fuel : Nat) (callable : CallableObjectFrame)
    (statement : AdmittedAutomaticDeclStmt) :
    FrameOutcome (Option IntegralValue) :=
  callable.frame.execute fuel statement.statement

/-- Execute a declaration fragment without closing the surrounding callable
parameter scope. -/
def executeDeclStmtInScope (fuel : Nat) (callable : CallableObjectFrame)
    (statement : AdmittedAutomaticDeclStmt) :
    FrameOutcome (Option IntegralValue) :=
  callable.frame.executeOpen fuel statement.statement

end CallableObjectFrame

end LeanModels.Cpp
