import LeanModels.Cpp.CallableFrame

namespace LeanModels.Cpp.CallableFrameTests

open LeanModels.Cpp
open IntegralObjectFrame
open AdmittedAutomaticDeclStmt
open CallableObjectFrame

private def handle (value : String) : FrontendHandle := {value}
private def intType : CppTypeEvidence := .builtin .int
private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩
private def declaration : Declaration := {
  id := "0x2", kind := "FunctionDecl", path := [0], name := some "f",
  lexicalParents := [], semanticParent := none, previousDecl := none,
  mangledName := none, type := none, location := none, range := none
}
private def parameter : CallableParameter := {
  declaration := handle "0x10", name := some "value", type := intType
}
private def function : CallableFunction := {
  occurrence := declaration,
  signature := {result := intType, parameters := [intType], variadic := false},
  parameters := [parameter], body := .skip
}

private def localReference : Raw := .object [
  ("id", .string "0x12"), ("kind", .string "DeclRefExpr"),
  ("referencedDecl", .object [("id", .string "0x10"), ("kind", .string "ParmVarDecl")])]

private def localVariable : Raw := .object [
  ("id", .string "0x11"), ("kind", .string "VarDecl"), ("init", .string "c"),
  ("inner", .array [localReference])]

private def localDeclStmt : Raw := .object [
  ("id", .string "0x20"), ("kind", .string "DeclStmt"),
  ("inner", .array [localVariable])]

private def localProbe : DeclarationProbe := {
  ast := .object [("id", .string "0x0"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [localDeclStmt])],
  metadata := .null, declarations := []
}

private def variableRow : CppVariableEvidence := {
  ordinal := 0, occurrence := handle "0x11", canonical := handle "0x11", kind := "VarDecl",
  isLocal := true, localOrParameter := true, storageClass := .none_,
  storageDuration := .automatic, tls := .none_, initStyle := .c,
  initializer := some {
    occurrence := handle "0x12", kind := "DeclRefExpr", sourceType := intType, type := intType},
  isConstexpr := false, attributeCount := 0
}

private def admittedLocal : Except String AdmittedAutomaticDeclStmt :=
  admit localProbe [
    {ordinal := 0, occurrence := handle "0x11", canonical := handle "0x11", type := intType}]
    [variableRow] [] TargetProfile.lp64 [handle "0x10"] [0]

private def parameterIsInitialized : Bool :=
  match CallableObjectFrame.start TargetProfile.lp64 function [signed 7] with
  | .ok callable =>
      match (callable.frame.read (handle "0x10")).result with
      | .ok value => value == signed 7
      | _ => false
  | .error _ => false

private def declarationExecutesAgainstParameter : Bool :=
  match CallableObjectFrame.start TargetProfile.lp64 function [signed 7], admittedLocal with
  | .ok callable, .ok statement =>
      let result := callable.executeDeclStmt 12 statement
      match result.result with
      | .ok none => result.frame.scopeDepth == 0 && result.frame.bound (handle "0x10") == false
      | _ => false
  | _, _ => false

private def invalidArgumentRemainsLoud : Bool :=
  let invalid : IntegralValue := ⟨.signed 0, 0⟩
  match CallableObjectFrame.start TargetProfile.lp64 function [invalid] with
  | .error (.argumentInvalid .zeroWidth) => true
  | _ => false

private def unsupportedParameterRemainsLoud : Bool :=
  let unsupported := {parameter with type := .pointer intType}
  let signature : CallableSignature :=
    {result := intType, parameters := [.pointer intType], variadic := false}
  let unsupportedFunction : CallableFunction :=
    {occurrence := declaration, signature, parameters := [unsupported], body := .skip}
  match CallableObjectFrame.start TargetProfile.lp64 unsupportedFunction [signed 7] with
  | .error (.argumentTypeMismatch declaration) => declaration == handle "0x10"
  | _ => false

#guard parameterIsInitialized
#guard declarationExecutesAgainstParameter
#guard invalidArgumentRemainsLoud
#guard unsupportedParameterRemainsLoud

end LeanModels.Cpp.CallableFrameTests
