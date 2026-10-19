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

/-- Execute a frontend-admitted declaration fragment in this callable frame. -/
def executeDeclStmt (fuel : Nat) (callable : CallableObjectFrame)
    (statement : AdmittedAutomaticDeclStmt) :
    FrameOutcome (Option IntegralValue) :=
  callable.frame.execute fuel statement.statement

end CallableObjectFrame

end LeanModels.Cpp
