import LeanModels.Cpp.AutomaticDeclarations

namespace LeanModels.Cpp.AutomaticDeclarationsTests

open LeanModels.Cpp
open IntegralObjectFrame
open AdmittedAutomaticDeclStmt

private def text (value : String) : Raw := .string value
private def object (fields : List (String × Raw)) : Raw := .object fields
private def handle (value : String) : FrontendHandle := {value}
private def intType : CppTypeEvidence := .builtin .int
private def typeRow (declaration : FrontendHandle) (type : CppTypeEvidence) : TypeEvidenceRow := {
  ordinal := 0, occurrence := declaration, canonical := declaration, type}

private def initializerEvidence (occurrence : FrontendHandle) (kind : String) :
    CppVariableInitializerEvidence := {
  occurrence, kind, sourceType := intType, type := intType
}

private def variableRow (declaration : FrontendHandle)
    (style : CppVariableInitStyle) (initializer : Option CppVariableInitializerEvidence) :
    CppVariableEvidence := {
  ordinal := 0, occurrence := declaration, canonical := declaration, kind := "VarDecl",
  isLocal := true, localOrParameter := true, storageClass := .none_,
  storageDuration := .automatic, tls := .none_, initStyle := style, initializer,
  isConstexpr := false, attributeCount := 0
}

private def literal (occurrence value : String) : Raw := object [
  ("id", text occurrence), ("kind", text "IntegerLiteral"), ("value", text value)]

private def reference (occurrence declaration : String) : Raw := object [
  ("id", text occurrence), ("kind", text "DeclRefExpr"),
  ("referencedDecl", object [("id", text declaration), ("kind", text "VarDecl")])]

private def cast (occurrence : String) (child : Raw) : Raw := object [
  ("id", text occurrence), ("kind", text "ImplicitCastExpr"),
  ("castKind", text "LValueToRValue"), ("inner", .array [child])]

private def varNode (declaration : String) (init : Option Raw) : Raw :=
  object (([("id", text declaration), ("kind", text "VarDecl")] ++
    (match init with
    | none => []
    | some value => [("init", text "c"), ("inner", .array [value])])) )

private def varNodeWithStyle (declaration style : String) (values : List Raw) : Raw :=
  object [("id", text declaration), ("kind", text "VarDecl"),
    ("init", text style), ("inner", .array values)]

private def declarationStmt (children : List Raw) : Raw := object [
  ("id", text "0x20"), ("kind", text "DeclStmt"), ("inner", .array children)]

private def probe (statement : Raw) : DeclarationProbe := {
  ast := object [("id", text "0x0"), ("kind", text "TranslationUnitDecl"),
    ("inner", .array [statement])], metadata := .null, declarations := []
}

private def admittedLiteral : Except String AdmittedAutomaticDeclStmt :=
  let declaration := handle "0x10"
  let initializer := initializerEvidence (handle "0x11") "IntegerLiteral"
  admit (probe (declarationStmt [varNode "0x10" (some (literal "0x11" "7"))]))
    [typeRow declaration intType] [variableRow declaration .c (some initializer)] []
    TargetProfile.lp64 [] [0]

private def admitsLiteral : Bool :=
  match admittedLiteral with
  | .ok result =>
      result.declarations == [handle "0x10"] &&
        match result.statement with
        | .declare declaration type source (.literal value) =>
            declaration == handle "0x10" && type == intType && source == intType &&
              value.value == 7
        | _ => false
  | .error _ => false

private def admitsMultipleAndReadsPrevious : Bool :=
  let first := handle "0x10"
  let second := handle "0x12"
  let firstInit := initializerEvidence (handle "0x11") "IntegerLiteral"
  let secondInit := initializerEvidence (handle "0x13") "ImplicitCastExpr"
  let source := declarationStmt [
    varNode "0x10" (some (literal "0x11" "7")),
    varNode "0x12" (some (cast "0x13" (reference "0x14" "0x10")))]
  let admitted := admit (probe source) [typeRow first intType, typeRow second intType]
    [variableRow first .c (some firstInit), variableRow second .c (some secondInit)] []
    TargetProfile.lp64 [] [0]
  match admitted with
  | .ok result =>
      result.declarations == [first, second] &&
        match result.statement with
        | .sequence (.declare left _ _ _) (.declare right _ _ (.read referenced)) =>
            left == first && right == second && referenced == first
        | _ => false
  | .error _ => false

private def admitsSelfInitializer : Bool :=
  let declaration := handle "0x10"
  let initializer := initializerEvidence (handle "0x11") "DeclRefExpr"
  match admit (probe (declarationStmt [varNode "0x10" (some (reference "0x11" "0x10"))]))
      [typeRow declaration intType] [variableRow declaration .c (some initializer)] []
      TargetProfile.lp64 [] [0] with
  | .ok result =>
      match result.statement with
      | .declare _ _ _ (.read _) => true
      | _ => false
  | .error _ => false

private def opened : Except FrameError IntegralObjectFrame := do
  let frame ← IntegralObjectFrame.empty TargetProfile.lp64
  let entered := frame.enterScope
  entered.result.map (fun _ => entered.frame)

private def selfInitializerRetainsStorage : Bool :=
  match (admit (probe (declarationStmt [varNode "0x10"
      (some (reference "0x11" "0x10"))]))
      [typeRow (handle "0x10") intType]
      [variableRow (handle "0x10") .c
        (some (initializerEvidence (handle "0x11") "DeclRefExpr"))] []
      TargetProfile.lp64 [] [0]), opened with
  | .ok admitted, .ok frame =>
      let result := frame.execute 8 admitted.statement
      (match result.result with
      | .error (.object (.lifetime .lifetimeNotStarted)) => true
      | _ => false) && result.frame.bound (handle "0x10") && result.frame.scopeDepth == 1
  | _, _ => false

private def admitsDefaultAndZero : Bool :=
  let defaultDeclaration := handle "0x10"
  let zeroDeclaration := handle "0x12"
  let zeroInitializer := initializerEvidence (handle "0x13") "InitListExpr"
  let source := declarationStmt [
    varNode "0x10" none,
    object [("id", text "0x12"), ("kind", text "VarDecl"), ("init", text "list"),
      ("inner", .array [object [("id", text "0x13"), ("kind", text "InitListExpr"),
        ("inner", .array [])]])]]
  let admitted := admit (probe source) [typeRow defaultDeclaration intType, typeRow zeroDeclaration intType]
    [variableRow defaultDeclaration .c none, variableRow zeroDeclaration .list (some zeroInitializer)] []
    TargetProfile.lp64 [] [0]
  match admitted with
  | .ok result =>
      match result.statement with
      | .sequence (.defaultDeclare first _) (.zeroDeclare second _) =>
          first == defaultDeclaration && second == zeroDeclaration
      | _ => false
  | .error _ => false

private def admitsDirectScalarForms : Bool :=
  let callDeclaration := handle "0x10"
  let parenDeclaration := handle "0x20"
  let callInitializer := initializerEvidence (handle "0x11") "IntegerLiteral"
  let parenInitializer := initializerEvidence (handle "0x21") "IntegerLiteral"
  let source := declarationStmt [
    varNodeWithStyle "0x10" "call" [literal "0x11" "7"],
    varNodeWithStyle "0x20" "paren-list" [literal "0x21" "9"]]
  let admitted := admit (probe source)
    [typeRow callDeclaration intType, typeRow parenDeclaration intType]
    [variableRow callDeclaration .call (some callInitializer),
      variableRow parenDeclaration .parenList (some parenInitializer)] []
    TargetProfile.lp64 [] [0]
  match admitted with
  | .ok result =>
      result.declarations == [callDeclaration, parenDeclaration] &&
        match result.statement with
        | .sequence (.declare call _ _ (.literal first))
            (.declare paren _ _ (.literal second)) =>
            call == callDeclaration && paren == parenDeclaration &&
              first.value == 7 && second.value == 9
        | _ => false
  | .error _ => false

private def rejectsMultiElementDirectScalar : Bool :=
  let declaration := handle "0x10"
  let initializer := initializerEvidence (handle "0x11") "InitListExpr"
  let source := declarationStmt [varNodeWithStyle "0x10" "paren-list" [
    literal "0x11" "1", literal "0x12" "2"]]
  (admit (probe source) [typeRow declaration intType]
    [variableRow declaration .parenList (some initializer)] [] TargetProfile.lp64 [] [0]) matches .error _

private def rejectsUnsupportedForms : Bool :=
  let declaration := handle "0x10"
  let initializer := initializerEvidence (handle "0x11") "CallExpr"
  let source := probe (declarationStmt [varNode "0x10" (some
    (object [("id", text "0x11"), ("kind", text "CallExpr"),
      ("inner", .array [])]))])
  let unsupportedCall := admit source [typeRow declaration intType]
    [variableRow declaration .call (some initializer)] [] TargetProfile.lp64 [] [0]
  let staticRow := {variableRow declaration .c (some (initializerEvidence (handle "0x11") "IntegerLiteral")) with
    storageDuration := .static_}
  let staticStorage := admit (probe (declarationStmt [varNode "0x10" (some (literal "0x11" "1"))]))
    [typeRow declaration intType] [staticRow] [] TargetProfile.lp64 [] [0]
  unsupportedCall matches .error _ && staticStorage matches .error _

private def rejectsBadJoin : Bool :=
  let declaration := handle "0x10"
  let source := probe (declarationStmt [object [("id", text "0x10"), ("kind", text "VarDecl")]])
  (admit source [] [variableRow declaration .c none] [] TargetProfile.lp64 [] [0]) matches .error _

#guard admitsLiteral
#guard admitsMultipleAndReadsPrevious
#guard admitsSelfInitializer
#guard selfInitializerRetainsStorage
#guard admitsDefaultAndZero
#guard admitsDirectScalarForms
#guard rejectsMultiElementDirectScalar
#guard rejectsUnsupportedForms
#guard rejectsBadJoin

-- Legacy root types cannot establish the operand type of a unary expression.
private def logicalInitializer (types : List CppInitializerExpressionType) :
    Except String AdmittedAutomaticDeclStmt :=
  let raw := object [("id", text "0x11"), ("kind", text "UnaryOperator"),
    ("opcode", text "!"), ("inner", .array [object [
      ("id", text "0x12"), ("kind", text "ImplicitCastExpr"),
      ("castKind", text "IntegralToBoolean"), ("inner", .array [literal "0x13" "2"])]])]
  let boolType : CppTypeEvidence := .builtin .boolean
  let initializer : CppVariableInitializerEvidence := {
    occurrence := handle "0x11", kind := "UnaryOperator", sourceType := boolType,
    type := boolType, expressionTypes := types}
  admit (probe (declarationStmt [varNode "0x10" (some raw)]))
    [typeRow (handle "0x10") intType]
    [variableRow (handle "0x10") .c (some initializer)] [] .lp64 [] [0]

private def logicalTypes : List CppInitializerExpressionType := [
  {occurrence := handle "0x11", kind := "UnaryOperator", type := .builtin .boolean},
  {occurrence := handle "0x12", kind := "ImplicitCastExpr", type := .builtin .boolean},
  {occurrence := handle "0x13", kind := "IntegerLiteral", type := intType}]

#guard logicalInitializer [] matches .error _
#guard logicalInitializer (logicalTypes.take 2) matches .error _
#guard match logicalInitializer logicalTypes, opened with
  | .ok admitted, .ok frame =>
      let result := frame.execute 12
        (.sequence admitted.statement (.return_ (.read (handle "0x10"))))
      (result.result matches .ok (some ⟨.signed 32, 0⟩))
  | _, _ => false

end LeanModels.Cpp.AutomaticDeclarationsTests
