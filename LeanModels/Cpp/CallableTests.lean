import LeanModels.Cpp.Callable
import LeanModels.Cpp.EvidenceTests

namespace LeanModels.Cpp.CallableTests

open LeanModels.Cpp
open LeanModels.Cpp.EvidenceTests

def fields (raw : Raw) (updates : List (String × Raw)) : Raw :=
  match raw with
  | .object entries => .object ((entries.filter fun entry =>
      !updates.any (fun update => update.1 == entry.1)) ++ updates)
  | _ => raw

def text (value : String) : Raw := .string value
def object (fields : List (String × Raw)) : Raw := .object fields
def builtin (name : String) : Raw := object [("kind", text "builtin"), ("name", text name)]

def rootRow : Raw := fields (commonRow "TranslationUnitDecl") [
  ("id", text "0x1"), ("canonical", text "0x1"),
  ("semantic_context", .null), ("lexical_context", .null)]

def parameterRow (id name : String) : Raw := fields (commonRow "ParmVarDecl") [
  ("id", text id), ("canonical", text id), ("name", text name),
  ("semantic_context", text "0x2"), ("lexical_context", text "0x2")]

def functionRowFor (name bodyKind : String) : Raw := fields functionRow [
  ("id", text "0x2"), ("canonical", text "0x2"), ("name", text name),
  ("semantic_context", text "0x1"), ("lexical_context", text "0x1"),
  ("definition", .bool true), ("body_present", .bool true),
  ("own_body_kind", text bodyKind), ("own_body_owner", text "0x2")]

def functionShapeFor (bodyKind : String) : FunctionShapeEvidence := {
  definition := true, bodyPresent := true, defaulted := false, deletedAsWritten := false,
  skippedBody := false, pendingBody := false, definingAttribute := false,
  lateParsed := false, explicitlyDefaulted := false, attributeCount := 0,
  ownBodyKind := some bodyKind, ownBodyOwner := some {value := "0x2"}}

def functionEvidence (name bodyKind : String) : DeclarationEvidenceRow := {
  ordinal := 1, id := {value := "0x2"}, kind := "FunctionDecl", canonical := {value := "0x2"},
  previous := none, semanticContext := some {value := "0x1"}, lexicalContext := some {value := "0x1"},
  implicit := false, dependentContext := false, owningModule := none,
  functionShape := some (functionShapeFor bodyKind), raw := functionRowFor name bodyKind}

def rootEvidence : DeclarationEvidenceRow := {
  ordinal := 0, id := {value := "0x1"}, kind := "TranslationUnitDecl", canonical := {value := "0x1"},
  previous := none, semanticContext := none, lexicalContext := none,
  implicit := false, dependentContext := false, owningModule := none,
  functionShape := none, raw := rootRow}

def parameterRaw (id name : String) : Raw := object [
  ("id", text id), ("kind", text "ParmVarDecl"), ("name", text name)]

def declRef (id name : String) : Raw := object [
  ("id", text id), ("kind", text "DeclRefExpr"),
  ("referencedDecl", object [("id", text id), ("kind", text "ParmVarDecl"), ("name", text name)])]

def implicitCast (id : String) (child : Raw) : Raw := object [
  ("id", text id), ("kind", text "ImplicitCastExpr"),
  ("castKind", text "LValueToRValue"), ("inner", .array [child])]

def returnStmt (id : String) (value : Raw) : Raw := object [
  ("id", text id), ("kind", text "ReturnStmt"), ("inner", .array [value])]

def body (statement : Raw) : Raw := object [
  ("id", text "0x30"), ("kind", text "CompoundStmt"), ("inner", .array [statement])]

def functionSource (name : String) (parameters : List Raw) (functionBody : Raw) : Raw := object [
  ("id", text "0x2"), ("kind", text "FunctionDecl"), ("name", text name),
  ("parentDeclContextId", text "0x1"),
  ("inner", .array (parameters ++ [functionBody]))]

def probeFor (source : Raw) (rows : List DeclarationEvidenceRow) : DeclarationProbe := {
  ast := object [("id", text "0x1"), ("kind", text "TranslationUnitDecl"),
    ("inner", .array [source])],
  metadata := object [], declarations := rows}

def intType : CppTypeEvidence := .builtin .int
def functionType (parameters : List CppTypeEvidence) : CppTypeEvidence :=
  .function intType parameters false

def typeRow (id : String) (type : CppTypeEvidence) : TypeEvidenceRow := {
  ordinal := 0, occurrence := {value := id}, canonical := {value := id}, type}

def identityProbe : DeclarationProbe :=
  probeFor (functionSource "identity" [parameterRaw "0x10" "value"]
    (body (returnStmt "0x31" (implicitCast "0x32" (declRef "0x10" "value")))))
    [rootEvidence, functionEvidence "identity" "CompoundStmt"]

def identityTypes : List TypeEvidenceRow := [
  typeRow "0x2" (functionType [intType]), typeRow "0x10" intType]

def literalProbe : DeclarationProbe :=
  probeFor (functionSource "literal" []
    (body (returnStmt "0x31" (object [
      ("id", text "0x32"), ("kind", text "IntegerLiteral"),
      ("type", object [("qualType", text "int")]), ("value", text "7")] ))))
    [rootEvidence, functionEvidence "literal" "CompoundStmt"]

def literalTypes : List TypeEvidenceRow := [typeRow "0x2" (functionType [])]

def binaryProbe : DeclarationProbe :=
  probeFor (functionSource "add" [parameterRaw "0x10" "left", parameterRaw "0x11" "right"]
    (body (returnStmt "0x31" (object [
      ("id", text "0x20"), ("kind", text "BinaryOperator"), ("opcode", text "+"),
      ("inner", .array [declRef "0x10" "left", declRef "0x11" "right"])]))))
    [rootEvidence, functionEvidence "add" "CompoundStmt"]

def binaryTypes : List TypeEvidenceRow := [
  typeRow "0x2" (functionType [intType, intType]), typeRow "0x10" intType,
  typeRow "0x11" intType]

def binaryEvidence : List CppBinaryExpressionEvidence := [{
  ordinal := 0, occurrence := {value := "0x20"}, operator := "+", result := intType,
  operands := [
    {occurrence := {value := "0x10"}, kind := "DeclRefExpr", sourceType := intType, type := intType},
    {occurrence := {value := "0x11"}, kind := "DeclRefExpr", sourceType := intType, type := intType}]}]

def typedParameter (id : String) : TypedCallableExpression := {
  expression := .parameter {value := id}, sourceType := intType, type := intType}

def admitIdentity : Except String CallableFunction :=
  admitCallableFunction identityProbe identityTypes [] TargetProfile.lp64 [0]

def admitLiteral : Except String CallableFunction :=
  admitCallableFunction literalProbe literalTypes [] TargetProfile.lp64 [0]

def admitBinary : Except String CallableFunction :=
  admitCallableFunction binaryProbe binaryTypes binaryEvidence TargetProfile.lp64 [0]

#guard match admitIdentity with
  | .ok function => function.parameters.length == 1
  | .error _ => false
#guard match admitIdentity with
  | .ok function => function.body.type == intType
  | .error _ => false
#guard match admitIdentity with
  | .ok function => function.body.expression == .parameter {value := "0x10"}
  | .error _ => false
#guard match admitIdentity with
  | .ok function => function.body.sourceType == intType
  | .error _ => false
#guard match admitLiteral with
  | .ok function => function.body.expression == .integer 7
  | .error _ => false
#guard match admitBinary with
  | .ok function => function.body.expression ==
      .binary "+" (typedParameter "0x10") (typedParameter "0x11")
  | .error _ => false
#guard match admitBinary with
  | .ok function =>
      match function.body.expression with
      | .binary _ left right =>
          left.sourceType == intType && left.type == intType &&
            right.sourceType == intType && right.type == intType
      | _ => false
  | .error _ => false
#guard (admitCallableFunction binaryProbe binaryTypes [] TargetProfile.lp64 [0]) matches .error _
#guard (admitCallableFunction
  (probeFor (functionSource "if_body" []
    (body (object [("id", text "0x33"), ("kind", text "IfStmt")])) )
    [rootEvidence, functionEvidence "if_body" "CompoundStmt"])
  [typeRow "0x2" (functionType [])] [] TargetProfile.lp64 [0]) matches .error _
#guard (admitCallableFunction
  (probeFor (functionSource "try_body" []
    (object [("id", text "0x30"), ("kind", text "CXXTryStmt"), ("inner", .array [])]))
    [rootEvidence, functionEvidence "try_body" "CXXTryStmt"])
  [typeRow "0x2" (functionType [])] [] TargetProfile.lp64 [0]) matches .error _

end LeanModels.Cpp.CallableTests
