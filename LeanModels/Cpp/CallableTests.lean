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

def declRefNode (id declaration name : String) : Raw := object [
  ("id", text id), ("kind", text "DeclRefExpr"),
  ("referencedDecl", object [("id", text declaration), ("kind", text "ParmVarDecl"),
    ("name", text name)])]

def implicitCastKind (id kind : String) (child : Raw) : Raw := object [
  ("id", text id), ("kind", text "ImplicitCastExpr"),
  ("castKind", text kind), ("inner", .array [child])]

def implicitCast (id : String) (child : Raw) : Raw :=
  implicitCastKind id "LValueToRValue" child

def returnStmt (id : String) (value : Raw) : Raw := object [
  ("id", text id), ("kind", text "ReturnStmt"), ("inner", .array [value])]

def integerLiteralRaw (id value : String) : Raw := object [
  ("id", text id), ("kind", text "IntegerLiteral"),
  ("type", object [("qualType", text "int")]), ("value", text value)]

def constantExprRaw (id value : String) : Raw := object [
  ("id", text id), ("kind", text "ConstantExpr"),
  ("type", object [("qualType", text "int")]), ("value", text value),
  ("inner", .array [integerLiteralRaw (id ++ "0") value])]

def caseRaw (id value : String) (body : List Raw) : Raw := object [
  ("id", text id), ("kind", text "CaseStmt"),
  ("inner", .array (constantExprRaw (id ++ "1") value :: body))]

def defaultRaw (id : String) (body : List Raw) : Raw := object [
  ("id", text id), ("kind", text "DefaultStmt"), ("inner", .array body)]

def compoundAssignRaw (id declaration leftId literalId literal : String) : Raw := object [
  ("id", text id), ("kind", text "CompoundAssignOperator"), ("opcode", text "+="),
  ("inner", .array [declRefNode leftId declaration "value",
    integerLiteralRaw literalId literal])]

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

def boolCastProbe : DeclarationProbe :=
  probeFor (functionSource "toBool" [parameterRaw "0x10" "value"]
    (body (returnStmt "0x31"
      (implicitCastKind "0x32" "IntegralToBoolean"
        (implicitCast "0x33" (declRef "0x10" "value"))))))
    [rootEvidence, functionEvidence "toBool" "CompoundStmt"]

def boolCastTypes : List TypeEvidenceRow := [
  typeRow "0x2" (.function (.builtin .boolean) [intType] false), typeRow "0x10" intType]

def admitBoolCast : Except String CallableFunction :=
  admitCallableFunction boolCastProbe boolCastTypes [] TargetProfile.lp64 [0]

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

def duplicateParameterProbe : DeclarationProbe :=
  probeFor (functionSource "duplicate" [parameterRaw "0x10" "left", parameterRaw "0x10" "right"]
    (body (returnStmt "0x31" (integerLiteralRaw "0x32" "0"))))
    [rootEvidence, functionEvidence "duplicate" "CompoundStmt"]

def duplicateParameterTypes : List TypeEvidenceRow := [
  typeRow "0x2" (functionType [intType, intType]), typeRow "0x10" intType]

#guard match admitCallableFunction duplicateParameterProbe duplicateParameterTypes []
    TargetProfile.lp64 [0] with
  | .error message => message == "callable: duplicate parameter declaration handle"
  | .ok _ => false

def duplicateLocalRaw : Raw := object [
  ("id", text "0x10"), ("kind", text "VarDecl"), ("init", text "c"),
  ("inner", .array [integerLiteralRaw "0x30" "1"])]

def duplicateLocalVariableEvidence : CppVariableEvidence := {
  ordinal := 0, occurrence := {value := "0x10"}, canonical := {value := "0x10"},
  kind := "VarDecl", isLocal := true, localOrParameter := true,
  storageClass := .none_, storageDuration := .automatic, tls := .none_, initStyle := .c,
  initializer := some {
    occurrence := {value := "0x30"}, kind := "IntegerLiteral",
    sourceType := intType, type := intType},
  isConstexpr := false, attributeCount := 0}

#guard match parseCallableStatementWithLocals
    {ast := .null, metadata := .null, declarations := []}
    [typeRow "0x10" intType] [duplicateLocalVariableEvidence] [] TargetProfile.lp64 intType
    [{declaration := {value := "0x10"}, name := some "value", type := intType}]
    (object [("id", text "0x20"), ("kind", text "DeclStmt"),
      ("inner", .array [duplicateLocalRaw])]) with
  | .error message => message == "callable: duplicate local declaration handle"
  | .ok _ => false

def admitLiteral : Except String CallableFunction :=
  admitCallableFunction literalProbe literalTypes [] TargetProfile.lp64 [0]

def admitBinary : Except String CallableFunction :=
  admitCallableFunction binaryProbe binaryTypes binaryEvidence TargetProfile.lp64 [0]

def assignmentProbe : DeclarationProbe :=
  probeFor (functionSource "bump" [parameterRaw "0x10" "value"] (object [
    ("id", text "0x30"), ("kind", text "CompoundStmt"),
    ("inner", .array [
      object [("id", text "0x50"), ("kind", text "BinaryOperator"), ("opcode", text "="),
        ("inner", .array [
          declRefNode "0x51" "0x10" "value",
          object [("id", text "0x20"), ("kind", text "BinaryOperator"), ("opcode", text "+"),
            ("inner", .array [
              declRefNode "0x43" "0x10" "value", integerLiteralRaw "0x44" "1"])]])],
      returnStmt "0x52" (implicitCast "0x53" (declRefNode "0x54" "0x10" "value"))])]))
    [rootEvidence, functionEvidence "bump" "CompoundStmt"]

def assignmentTypes : List TypeEvidenceRow := [
  typeRow "0x2" (functionType [intType]), typeRow "0x10" intType]

def assignmentEvidence : List CppBinaryExpressionEvidence := [{
  ordinal := 0, occurrence := {value := "0x20"}, operator := "+", result := intType,
  operands := [
    {occurrence := {value := "0x43"}, kind := "DeclRefExpr", sourceType := intType, type := intType},
    {occurrence := {value := "0x44"}, kind := "IntegerLiteral", sourceType := intType, type := intType}]}]

def admitAssignment : Except String CallableFunction :=
  admitCallableFunction assignmentProbe assignmentTypes assignmentEvidence TargetProfile.lp64 [0]

def incrementRaw (id operator : String) (isPostfix : Bool) (child : Raw) : Raw := object [
  ("id", text id), ("kind", text "UnaryOperator"), ("opcode", text operator),
  ("isPostfix", .bool isPostfix), ("inner", .array [child])]

def prefixIncrementProbe : DeclarationProbe :=
  probeFor (functionSource "prefix" [parameterRaw "0x10" "value"]
    (body (returnStmt "0x31"
      (implicitCast "0x32" (incrementRaw "0x20" "++" false
        (declRefNode "0x21" "0x10" "value"))))))
    [rootEvidence, functionEvidence "prefix" "CompoundStmt"]

def postfixIncrementProbe : DeclarationProbe :=
  probeFor (functionSource "postfix" [parameterRaw "0x10" "value"]
    (body (returnStmt "0x31"
      (implicitCast "0x32" (incrementRaw "0x20" "++" true
        (declRefNode "0x21" "0x10" "value"))))))
    [rootEvidence, functionEvidence "postfix" "CompoundStmt"]

def decrementProbe : DeclarationProbe :=
  probeFor (functionSource "decrement" [parameterRaw "0x10" "value"]
    (body (returnStmt "0x31"
      (incrementRaw "0x20" "--" false (declRefNode "0x21" "0x10" "value")))))
    [rootEvidence, functionEvidence "decrement" "CompoundStmt"]

def incrementTypes : List TypeEvidenceRow := [
  typeRow "0x2" (functionType [intType]), typeRow "0x10" intType]

def admitPrefixIncrement : Except String CallableFunction :=
  admitCallableFunction prefixIncrementProbe incrementTypes [] TargetProfile.lp64 [0]

def admitPostfixIncrement : Except String CallableFunction :=
  admitCallableFunction postfixIncrementProbe incrementTypes [] TargetProfile.lp64 [0]

def admitDecrement : Except String CallableFunction :=
  admitCallableFunction decrementProbe incrementTypes [] TargetProfile.lp64 [0]

def conditionalProbe : DeclarationProbe :=
  probeFor (functionSource "select" [parameterRaw "0x10" "value"]
    (body (returnStmt "0x31" (object [
      ("id", text "0x20"), ("kind", text "ConditionalOperator"),
      ("inner", .array [declRefNode "0x21" "0x10" "value",
        integerLiteralRaw "0x22" "7", integerLiteralRaw "0x23" "3"])]))))
    [rootEvidence, functionEvidence "select" "CompoundStmt"]

def admitConditional : Except String CallableFunction :=
  admitCallableFunction conditionalProbe incrementTypes [] TargetProfile.lp64 [0]

def commaProbe : DeclarationProbe :=
  probeFor (functionSource "comma" [parameterRaw "0x10" "value"]
    (body (returnStmt "0x31" (object [
      ("id", text "0x20"), ("kind", text "BinaryOperator"), ("opcode", text ","),
      ("inner", .array [
        incrementRaw "0x21" "++" true (declRefNode "0x22" "0x10" "value"),
        declRefNode "0x23" "0x10" "value"])]))))
    [rootEvidence, functionEvidence "comma" "CompoundStmt"]

def commaEvidence : List CppBinaryExpressionEvidence := [{
  ordinal := 0, occurrence := {value := "0x20"}, operator := ",", result := intType,
  operands := [
    {occurrence := {value := "0x21"}, kind := "UnaryOperator", sourceType := intType, type := intType},
    {occurrence := {value := "0x23"}, kind := "DeclRefExpr", sourceType := intType, type := intType}]}]

def admitComma : Except String CallableFunction :=
  admitCallableFunction commaProbe incrementTypes commaEvidence TargetProfile.lp64 [0]

#guard admitPrefixIncrement.isOk
#guard admitPostfixIncrement.isOk
#guard admitDecrement.isOk
#guard admitConditional.isOk
#guard admitComma.isOk

def compoundAssignmentProbe : DeclarationProbe :=
  probeFor (functionSource "bumpBy" [parameterRaw "0x10" "value"] (object [
    ("id", text "0x30"), ("kind", text "CompoundStmt"),
    ("inner", .array [
      object [
        ("id", text "0x50"), ("kind", text "CompoundAssignOperator"),
        ("opcode", text "+="), ("inner", .array [
          declRefNode "0x51" "0x10" "value", integerLiteralRaw "0x44" "1"])
      ],
      returnStmt "0x52" (implicitCast "0x53" (declRefNode "0x54" "0x10" "value"))
    ])
  ])) [rootEvidence, functionEvidence "bumpBy" "CompoundStmt"]

def compoundAssignmentEvidence : List CppBinaryExpressionEvidence := [{
  ordinal := 0, occurrence := {value := "0x50"}, operator := "+=", result := intType,
  operands := [
    {occurrence := {value := "0x51"}, kind := "DeclRefExpr", sourceType := intType, type := intType},
    {occurrence := {value := "0x44"}, kind := "IntegerLiteral", sourceType := intType, type := intType}]}]

def admitCompoundAssignment : Except String CallableFunction :=
  admitCallableFunction compoundAssignmentProbe assignmentTypes compoundAssignmentEvidence
    TargetProfile.lp64 [0]

private def parseCompoundAssignmentTarget (target : Raw)
    (rows : List CppBinaryExpressionEvidence) : Except String CallableStatement :=
  parseCallableStatement .lp64
    [{declaration := {value := "0x10"}, name := some "value", type := intType}]
    rows intType (object [
      ("id", text "0x50"), ("kind", text "CompoundAssignOperator"), ("opcode", text "+="),
      ("inner", .array [target, integerLiteralRaw "0x44" "1"])])

#guard (parseCompoundAssignmentTarget (declRefNode "0x51" "0x10" "value") []) matches .error _
#guard (parseCompoundAssignmentTarget (declRefNode "0x51" "0x99" "value")
  compoundAssignmentEvidence) matches .error _
#guard (parseCompoundAssignmentTarget (declRefNode "0x99" "0x10" "value")
  compoundAssignmentEvidence) matches .error _
#guard (parseCompoundAssignmentTarget (integerLiteralRaw "0x51" "1")
  compoundAssignmentEvidence) matches .error _
#guard (parseCompoundAssignmentTarget (declRefNode "0x51" "0x10" "value")
  (compoundAssignmentEvidence.map fun row => {row with operands := row.operands.reverse}))
  matches .error _
#guard (parseCompoundAssignmentTarget (declRefNode "0x51" "0x10" "value")
  (compoundAssignmentEvidence.map fun row => {row with result := .builtin .unsignedInt}))
  matches .error _

def ifProbe : DeclarationProbe :=
  probeFor (functionSource "choose" []
    (body (object [
      ("id", text "0x33"), ("kind", text "IfStmt"),
      ("inner", .array [integerLiteralRaw "0x40" "1",
        body (returnStmt "0x41" (integerLiteralRaw "0x42" "7")),
        body (returnStmt "0x43" (integerLiteralRaw "0x44" "8"))])])) )
    [rootEvidence, functionEvidence "choose" "CompoundStmt"]

def ifTypes : List TypeEvidenceRow := [typeRow "0x2" (functionType [])]

def admitIf : Except String CallableFunction :=
  admitCallableFunction ifProbe ifTypes [] TargetProfile.lp64 [0]

def whileProbe : DeclarationProbe :=
  probeFor (functionSource "loop" [parameterRaw "0x10" "value"] (object [
    ("id", text "0x31"), ("kind", text "CompoundStmt"),
    ("inner", .array [
      object [
        ("id", text "0x50"), ("kind", text "WhileStmt"),
        ("inner", .array [
          implicitCast "0x51" (declRef "0x10" "value"),
          body (returnStmt "0x52" (implicitCast "0x53" (declRef "0x10" "value")))])],
      returnStmt "0x54" (integerLiteralRaw "0x55" "0")])]))
    [rootEvidence, functionEvidence "loop" "CompoundStmt"]

def whileTypes : List TypeEvidenceRow := [
  typeRow "0x2" (functionType [intType]), typeRow "0x10" intType]

def admitWhile : Except String CallableFunction :=
  admitCallableFunction whileProbe whileTypes [] TargetProfile.lp64 [0]

def doProbe : DeclarationProbe :=
  probeFor (functionSource "doLoop" [parameterRaw "0x10" "value"] (object [
    ("id", text "0x31"), ("kind", text "CompoundStmt"),
    ("inner", .array [
      object [
        ("id", text "0x50"), ("kind", text "DoStmt"),
        ("inner", .array [
          body (object [("id", text "0x52"), ("kind", text "NullStmt")]),
          implicitCast "0x51" (declRef "0x10" "value")])],
      returnStmt "0x54" (integerLiteralRaw "0x55" "7")])]))
    [rootEvidence, functionEvidence "doLoop" "CompoundStmt"]

def doTypes : List TypeEvidenceRow := [
  typeRow "0x2" (functionType [intType]), typeRow "0x10" intType]

def admitDo : Except String CallableFunction :=
  admitCallableFunction doProbe doTypes [] TargetProfile.lp64 [0]

def forProbe : DeclarationProbe :=
  probeFor (functionSource "forLoop" [parameterRaw "0x10" "value"] (object [
    ("id", text "0x31"), ("kind", text "CompoundStmt"),
    ("inner", .array [
      object [
        ("id", text "0x50"), ("kind", text "ForStmt"),
        ("inner", .array [
          object [
            ("id", text "0x51"), ("kind", text "BinaryOperator"), ("opcode", text "="),
            ("inner", .array [declRefNode "0x52" "0x10" "value", integerLiteralRaw "0x53" "0"])],
          object [],
          object [
            ("id", text "0x54"), ("kind", text "BinaryOperator"), ("opcode", text "<"),
            ("inner", .array [implicitCast "0x55" (declRefNode "0x56" "0x10" "value"),
              integerLiteralRaw "0x57" "3"])],
          incrementRaw "0x58" "++" false (declRefNode "0x59" "0x10" "value"),
          body (object [
            ("id", text "0x5a"), ("kind", text "CompoundAssignOperator"),
            ("opcode", text "+="),
            ("inner", .array [declRefNode "0x5b" "0x10" "value",
              integerLiteralRaw "0x5c" "1"])])])],
      returnStmt "0x5d" (implicitCast "0x5e" (declRefNode "0x5f" "0x10" "value"))])]))
    [rootEvidence, functionEvidence "forLoop" "CompoundStmt"]

def forBreakProbe : DeclarationProbe :=
  probeFor (functionSource "forBreak" [parameterRaw "0x10" "value"] (object [
    ("id", text "0xa1"), ("kind", text "CompoundStmt"),
    ("inner", .array [
      object [
        ("id", text "0xa0"), ("kind", text "ForStmt"),
        ("inner", .array [
          object [
            ("id", text "0xa2"), ("kind", text "BinaryOperator"), ("opcode", text "="),
            ("inner", .array [declRefNode "0xa3" "0x10" "value",
              integerLiteralRaw "0xa4" "0"])],
          object [],
          object [
            ("id", text "0xa6"), ("kind", text "BinaryOperator"), ("opcode", text "<"),
            ("inner", .array [implicitCast "0xa7" (declRefNode "0xa8" "0x10" "value"),
              integerLiteralRaw "0xa9" "3"])],
          incrementRaw "0xaa" "++" false (declRefNode "0xab" "0x10" "value"),
          body (object [
            ("id", text "0xac"), ("kind", text "CompoundStmt"),
            ("inner", .array [
              incrementRaw "0xad" "++" false (declRefNode "0xae" "0x10" "value"),
              object [("id", text "0xaf"), ("kind", text "BreakStmt")]])])])],
      returnStmt "0xb0" (implicitCast "0xb1" (declRefNode "0xb2" "0x10" "value"))])]))
    [rootEvidence, functionEvidence "forBreak" "CompoundStmt"]

def forContinueProbe : DeclarationProbe :=
  probeFor (functionSource "forContinue" [parameterRaw "0x10" "value"] (object [
    ("id", text "0xc1"), ("kind", text "CompoundStmt"),
    ("inner", .array [
      object [
        ("id", text "0xc0"), ("kind", text "ForStmt"),
        ("inner", .array [
          object [
            ("id", text "0xc2"), ("kind", text "BinaryOperator"), ("opcode", text "="),
            ("inner", .array [declRefNode "0xc3" "0x10" "value",
              integerLiteralRaw "0xc4" "0"])],
          object [],
          object [
            ("id", text "0xc6"), ("kind", text "BinaryOperator"), ("opcode", text "<"),
            ("inner", .array [implicitCast "0xc7" (declRefNode "0xc8" "0x10" "value"),
              integerLiteralRaw "0xc9" "3"])],
          incrementRaw "0xca" "++" false (declRefNode "0xcb" "0x10" "value"),
          body (object [
            ("id", text "0xcc"), ("kind", text "CompoundStmt"),
            ("inner", .array [object [("id", text "0xcd"), ("kind", text "ContinueStmt")]])])])],
      returnStmt "0xd0" (implicitCast "0xd1" (declRefNode "0xd2" "0x10" "value"))])]))
    [rootEvidence, functionEvidence "forContinue" "CompoundStmt"]

def forTypes : List TypeEvidenceRow := [
  typeRow "0x2" (functionType [intType]), typeRow "0x10" intType]

def forEvidence : List CppBinaryExpressionEvidence := [
  {ordinal := 0, occurrence := {value := "0x54"}, operator := "<", result := .builtin .boolean,
    operands := [
      {occurrence := {value := "0x55"}, kind := "ImplicitCastExpr", sourceType := intType, type := intType},
      {occurrence := {value := "0x57"}, kind := "IntegerLiteral", sourceType := intType, type := intType}]},
  {ordinal := 1, occurrence := {value := "0x5a"}, operator := "+=", result := intType,
    operands := [
      {occurrence := {value := "0x5b"}, kind := "DeclRefExpr", sourceType := intType, type := intType},
      {occurrence := {value := "0x5c"}, kind := "IntegerLiteral", sourceType := intType, type := intType}]}]

def admitFor : Except String CallableFunction :=
  admitCallableFunction forProbe forTypes forEvidence TargetProfile.lp64 [0]

#guard admitFor.isOk

def breakProbe : DeclarationProbe :=
  probeFor (functionSource "breakLoop" [parameterRaw "0x10" "value"] (object [
    ("id", text "0x31"), ("kind", text "CompoundStmt"),
    ("inner", .array [
      object [
        ("id", text "0x50"), ("kind", text "WhileStmt"),
        ("inner", .array [
          object [
            ("id", text "0x51"), ("kind", text "BinaryOperator"), ("opcode", text "<"),
            ("inner", .array [implicitCast "0x52" (declRefNode "0x53" "0x10" "value"),
              integerLiteralRaw "0x54" "3"])],
          body (object [
            ("id", text "0x55"), ("kind", text "CompoundStmt"),
            ("inner", .array [
              incrementRaw "0x56" "++" false (declRefNode "0x57" "0x10" "value"),
              object [("id", text "0x58"), ("kind", text "BreakStmt")]])])])],
      returnStmt "0x59" (implicitCast "0x5a" (declRefNode "0x5b" "0x10" "value"))])]))
    [rootEvidence, functionEvidence "breakLoop" "CompoundStmt"]

def continueProbe : DeclarationProbe :=
  probeFor (functionSource "continueLoop" [parameterRaw "0x10" "value"] (object [
    ("id", text "0x61"), ("kind", text "CompoundStmt"),
    ("inner", .array [
      object [
        ("id", text "0x70"), ("kind", text "WhileStmt"),
        ("inner", .array [
          object [
            ("id", text "0x71"), ("kind", text "BinaryOperator"), ("opcode", text "<"),
            ("inner", .array [implicitCast "0x72" (declRefNode "0x73" "0x10" "value"),
              integerLiteralRaw "0x74" "3"])],
          body (object [
            ("id", text "0x75"), ("kind", text "CompoundStmt"),
            ("inner", .array [
              incrementRaw "0x76" "++" false (declRefNode "0x77" "0x10" "value"),
              object [("id", text "0x78"), ("kind", text "ContinueStmt")]])])])],
      returnStmt "0x79" (implicitCast "0x7a" (declRefNode "0x7b" "0x10" "value"))])]))
    [rootEvidence, functionEvidence "continueLoop" "CompoundStmt"]

def transferTypes : List TypeEvidenceRow := [
  typeRow "0x2" (functionType [intType]), typeRow "0x10" intType]

def transferEvidence (occurrence : String) (leftOccurrence : String) (literalOccurrence : String) :
    List CppBinaryExpressionEvidence := [{
      ordinal := 0, occurrence := {value := occurrence}, operator := "<", result := .builtin .boolean,
      operands := [
        {occurrence := {value := leftOccurrence}, kind := "ImplicitCastExpr",
          sourceType := intType, type := intType},
        {occurrence := {value := literalOccurrence}, kind := "IntegerLiteral",
          sourceType := intType, type := intType}]}]

def forBreakEvidence : List CppBinaryExpressionEvidence :=
  transferEvidence "0xa6" "0xa7" "0xa9"

def forContinueEvidence : List CppBinaryExpressionEvidence :=
  transferEvidence "0xc6" "0xc7" "0xc9"

def admitForBreak : Except String CallableFunction :=
  admitCallableFunction forBreakProbe forTypes forBreakEvidence TargetProfile.lp64 [0]

def admitForContinue : Except String CallableFunction :=
  admitCallableFunction forContinueProbe forTypes forContinueEvidence TargetProfile.lp64 [0]

#guard admitForBreak.isOk
#guard admitForContinue.isOk

def switchBody : Raw := object [
  ("id", text "0xe4"), ("kind", text "CompoundStmt"),
  ("inner", .array [
    caseRaw "0xe5" "0" [returnStmt "0xe6" (integerLiteralRaw "0xe7" "4")],
    caseRaw "0xe8" "1" [compoundAssignRaw "0xe9" "0x10" "0xea" "0xeb" "2"],
    caseRaw "0xec" "2" [object [("id", text "0xed0"), ("kind", text "BreakStmt")]],
    defaultRaw "0xee" [compoundAssignRaw "0xef" "0x10" "0xf0" "0xf5" "3"]])]

def switchStatement : Raw := object [
  ("id", text "0xe0"), ("kind", text "SwitchStmt"),
  ("inner", .array [implicitCast "0xe2" (declRefNode "0xe3" "0x10" "value"),
    switchBody])]

def switchProbe : DeclarationProbe :=
  probeFor (functionSource "switchProbe" [parameterRaw "0x10" "value"] (object [
    ("id", text "0xe1"), ("kind", text "CompoundStmt"),
    ("inner", .array [switchStatement,
      returnStmt "0xf1" (implicitCast "0xf2" (declRefNode "0xf3" "0x10" "value"))])]))
    [rootEvidence, functionEvidence "switchProbe" "CompoundStmt"]

def switchTypes : List TypeEvidenceRow := [
  typeRow "0x2" (functionType [intType]), typeRow "0x10" intType]

def switchEvidence : List CppBinaryExpressionEvidence := [
  {ordinal := 0, occurrence := {value := "0xe9"}, operator := "+=", result := intType,
    operands := [
      {occurrence := {value := "0xea"}, kind := "DeclRefExpr", sourceType := intType, type := intType},
      {occurrence := {value := "0xeb"}, kind := "IntegerLiteral", sourceType := intType, type := intType}]},
  {ordinal := 1, occurrence := {value := "0xef"}, operator := "+=", result := intType,
    operands := [
      {occurrence := {value := "0xf0"}, kind := "DeclRefExpr", sourceType := intType, type := intType},
      {occurrence := {value := "0xf5"}, kind := "IntegerLiteral", sourceType := intType, type := intType}]}]

def admitSwitch : Except String CallableFunction :=
  admitCallableFunction switchProbe switchTypes switchEvidence TargetProfile.lp64 [0]

#guard admitSwitch.isOk

private def parseSwitchClauses (clauses : List Raw) : Except String CallableStatement :=
  parseCallableStatement TargetProfile.lp64
    [{declaration := {value := "0x10"}, name := some "value", type := intType}]
    [] intType (fields switchStatement [
      ("inner", .array [implicitCast "0xe2" (declRefNode "0xe3" "0x10" "value"),
        fields switchBody [("inner", .array clauses)]])])

private def switchRefuses (clauses : List Raw) (message : String) : Bool :=
  match parseSwitchClauses clauses with
  | .error reason => reason == message
  | .ok _ => false

#guard parseSwitchClauses [
  caseRaw "0x100" "0" [returnStmt "0x101" (integerLiteralRaw "0x102" "4")],
  caseRaw "0x110" "1" [returnStmt "0x111" (integerLiteralRaw "0x112" "5")],
  defaultRaw "0x120" [returnStmt "0x121" (integerLiteralRaw "0x122" "6")]] |>.isOk

#guard switchRefuses [
  caseRaw "0x100" "0" [], caseRaw "0x110" "1" [], caseRaw "0x120" "1" []]
    "callable: switch labels must be unique with at most one default"

#guard switchRefuses [
  caseRaw "0x100" "0" [], defaultRaw "0x110" [], defaultRaw "0x120" []]
    "callable: switch labels must be unique with at most one default"

#guard switchRefuses [
  defaultRaw "0x100" [], caseRaw "0x110" "1" [], caseRaw "0x120" "1" []]
    "callable: switch labels must be unique with at most one default"

#guard parseSwitchClauses [
  caseRaw "0x100" "0" [object [("kind", text "ContinueStmt")]]] |>.isOk

#guard parseSwitchClauses [
  defaultRaw "0x100" [object [("kind", text "CompoundStmt"),
    ("inner", .array [object [("kind", text "CompoundStmt"),
      ("inner", .array [object [("kind", text "ContinueStmt")]])]])]]] |>.isOk

#guard parseSwitchClauses [
  defaultRaw "0x100" [object [("kind", text "NullStmt"),
    ("annotation", text "ContinueStmt")]]] |>.isOk

def admitBreak : Except String CallableFunction :=
  admitCallableFunction breakProbe transferTypes (transferEvidence "0x51" "0x52" "0x54")
    TargetProfile.lp64 [0]

def admitContinue : Except String CallableFunction :=
  admitCallableFunction continueProbe transferTypes (transferEvidence "0x71" "0x72" "0x74")
    TargetProfile.lp64 [0]

#guard admitBreak.isOk
#guard admitContinue.isOk

def doBreakProbe : DeclarationProbe :=
  probeFor (functionSource "doBreak" [parameterRaw "0x10" "value"] (object [
    ("id", text "0x81"), ("kind", text "CompoundStmt"),
    ("inner", .array [
      object [
        ("id", text "0x80"), ("kind", text "DoStmt"),
        ("inner", .array [
          body (object [
            ("id", text "0x82"), ("kind", text "CompoundStmt"),
            ("inner", .array [
              incrementRaw "0x83" "++" false (declRefNode "0x84" "0x10" "value"),
              object [("id", text "0x85"), ("kind", text "BreakStmt")]])]),
          object [
            ("id", text "0x86"), ("kind", text "BinaryOperator"), ("opcode", text "<"),
            ("inner", .array [implicitCast "0x87" (declRefNode "0x88" "0x10" "value"),
              integerLiteralRaw "0x89" "3"])]])],
      returnStmt "0x8a" (implicitCast "0x8b" (declRefNode "0x8c" "0x10" "value"))])]))
    [rootEvidence, functionEvidence "doBreak" "CompoundStmt"]

def doContinueProbe : DeclarationProbe :=
  probeFor (functionSource "doContinue" [parameterRaw "0x10" "value"] (object [
    ("id", text "0x91"), ("kind", text "CompoundStmt"),
    ("inner", .array [
      object [
        ("id", text "0x90"), ("kind", text "DoStmt"),
        ("inner", .array [
          body (object [
            ("id", text "0x92"), ("kind", text "CompoundStmt"),
            ("inner", .array [
              incrementRaw "0x93" "++" false (declRefNode "0x94" "0x10" "value"),
              object [("id", text "0x95"), ("kind", text "ContinueStmt")]])]),
          object [
            ("id", text "0x96"), ("kind", text "BinaryOperator"), ("opcode", text "<"),
            ("inner", .array [implicitCast "0x97" (declRefNode "0x98" "0x10" "value"),
              integerLiteralRaw "0x99" "3"])]])],
      returnStmt "0x9a" (implicitCast "0x9b" (declRefNode "0x9c" "0x10" "value"))])]))
    [rootEvidence, functionEvidence "doContinue" "CompoundStmt"]

def admitDoBreak : Except String CallableFunction :=
  admitCallableFunction doBreakProbe transferTypes (transferEvidence "0x86" "0x87" "0x89")
    TargetProfile.lp64 [0]

def admitDoContinue : Except String CallableFunction :=
  admitCallableFunction doContinueProbe transferTypes (transferEvidence "0x96" "0x97" "0x99")
    TargetProfile.lp64 [0]

#guard admitDoBreak.isOk
#guard admitDoContinue.isOk

def unaryProbe : DeclarationProbe :=
  probeFor (functionSource "negate" [parameterRaw "0x10" "value"]
    (body (returnStmt "0x31" (object [
      ("id", text "0x32"), ("kind", text "UnaryOperator"), ("opcode", text "-"),
      ("inner", .array [implicitCast "0x33" (declRef "0x10" "value")])]))))
    [rootEvidence, functionEvidence "negate" "CompoundStmt"]

def unaryTypes : List TypeEvidenceRow := [
  typeRow "0x2" (functionType [intType]), typeRow "0x10" intType]

def admitUnary : Except String CallableFunction :=
  admitCallableFunction unaryProbe unaryTypes [] TargetProfile.lp64 [0]

-- Value conversion removes constness without changing the object descriptor.
#guard match parseCallableExpression .lp64
    [{declaration := {value := "0x10"}, name := some "value",
      type := .qualified true false intType}] []
    (implicitCast "0x33" (declRefNode "0x34" "0x10" "value")) none (some intType) with
  | .ok expression => expression.type == intType &&
      expression.sourceType == .qualified true false intType
  | .error _ => false

#guard (parseCallableExpression .lp64
    [{declaration := {value := "0x10"}, name := some "value",
      type := .qualified false true intType}] []
    (implicitCast "0x33" (declRefNode "0x34" "0x10" "value")) none (some intType)) matches .error _

def logicalProbe : DeclarationProbe :=
  probeFor (functionSource "both" [parameterRaw "0x10" "left", parameterRaw "0x11" "right"]
    (body (returnStmt "0x31" (object [
      ("id", text "0x20"), ("kind", text "BinaryOperator"), ("opcode", text "&&"),
      ("inner", .array [declRef "0x10" "left", declRef "0x11" "right"])]))))
    [rootEvidence, functionEvidence "both" "CompoundStmt"]

def logicalTypes : List TypeEvidenceRow := [
  typeRow "0x2" (.function (.builtin .boolean) [intType, intType] false),
  typeRow "0x10" intType, typeRow "0x11" intType]

def logicalEvidence : List CppBinaryExpressionEvidence := [{
  ordinal := 0, occurrence := {value := "0x20"}, operator := "&&", result := .builtin .boolean,
  operands := [
    {occurrence := {value := "0x10"}, kind := "DeclRefExpr", sourceType := intType, type := intType},
    {occurrence := {value := "0x11"}, kind := "DeclRefExpr", sourceType := intType, type := intType}]}]

def admitLogical : Except String CallableFunction :=
  admitCallableFunction logicalProbe logicalTypes logicalEvidence TargetProfile.lp64 [0]

def logicalEffectProbe (operator : String) (name : String) : DeclarationProbe :=
  probeFor (functionSource name [parameterRaw "0x10" "value"]
    (body (returnStmt "0x31" (object [
      ("id", text "0x20"), ("kind", text "BinaryOperator"), ("opcode", text operator),
      ("inner", .array [
        implicitCastKind "0x21" "IntegralToBoolean" (declRefNode "0x22" "0x10" "value"),
        implicitCastKind "0x23" "IntegralToBoolean"
          (incrementRaw "0x24" "++" false (declRefNode "0x25" "0x10" "value"))])]))))
    [rootEvidence, functionEvidence name "CompoundStmt"]

def logicalEffectTypes : List TypeEvidenceRow := [
  typeRow "0x2" (.function (.builtin .boolean) [intType] false), typeRow "0x10" intType]

def logicalEffectEvidence (operator : String) : List CppBinaryExpressionEvidence := [{
  ordinal := 0, occurrence := {value := "0x20"}, operator, result := .builtin .boolean,
  operands := [
    {occurrence := {value := "0x21"}, kind := "ImplicitCastExpr", sourceType := intType,
      type := .builtin .boolean},
    {occurrence := {value := "0x23"}, kind := "ImplicitCastExpr", sourceType := intType,
      type := .builtin .boolean}]}]

def admitLogicalEffect (operator : String) (name : String) : Except String CallableFunction :=
  admitCallableFunction (logicalEffectProbe operator name) logicalEffectTypes
    (logicalEffectEvidence operator) TargetProfile.lp64 [0]

#guard (admitLogicalEffect "&&" "bothIncrement").isOk
#guard (admitLogicalEffect "||" "eitherIncrement").isOk

#guard match admitIdentity with
  | .ok function => function.parameters.length == 1
  | .error _ => false
#guard match admitBoolCast with
  | .ok function =>
      match function.body with
      | .block (.return_ expression) =>
          expression.type == .builtin .boolean &&
            match expression.expression with
            | .convert _ => true
            | _ => false
      | _ => false
  | .error _ => false
#guard match admitIdentity with
  | .ok function =>
      match function.body with
      | .block (.return_ expression) => expression.type == intType
      | _ => false
  | .error _ => false
#guard match admitIdentity with
  | .ok function =>
      match function.body with
      | .block (.return_ expression) => expression.expression == .parameter {value := "0x10"}
      | _ => false
  | .error _ => false
#guard match admitIdentity with
  | .ok function =>
      match function.body with
      | .block (.return_ expression) => expression.sourceType == intType
      | _ => false
  | .error _ => false
#guard match admitLiteral with
  | .ok function =>
      match function.body with
      | .block (.return_ expression) => expression.expression == .integer 7
      | _ => false
  | .error _ => false
#guard match admitBinary with
  | .ok function =>
      match function.body with
      | .block (.return_ expression) => expression.expression ==
          .binary "+" (typedParameter "0x10") (typedParameter "0x11")
      | _ => false
  | .error _ => false
#guard CallableExpression.hasEffects
  (.binary "+"
    {expression := .increment "++" true {value := "0x10"}, sourceType := intType, type := intType}
    {expression := .integer 1, sourceType := intType, type := intType})
#guard match admitAssignment with
  | .ok function =>
      match function.body with
      | .block (.sequence (.assign declaration expression) (.return_ _)) =>
          declaration == {value := "0x10"} && expression.type == intType
      | _ => false
  | .error _ => false
#guard match admitCompoundAssignment with
  | .ok function =>
      match function.body with
      | .block (.sequence (.compoundAssign operator declaration _) (.return_ _)) =>
          operator == "+=" && declaration == {value := "0x10"}
      | _ => false
  | .error _ => false
#guard match admitIf with
  | .ok function =>
      match function.body with
      | .block (.conditional condition (.block (.return_ _)) (.block (.return_ _))) =>
          condition.expression == .integer 1
      | _ => false
  | .error _ => false
#guard match admitWhile with
  | .ok function =>
      match function.body with
      | .block (.sequence (.whileLoop _ (.block (.return_ _))) (.return_ _)) => true
      | _ => false
  | .error _ => false
#guard match admitDo with
  | .ok function =>
      match function.body with
      | .block (.sequence (.doWhile (.block .skip) _) (.return_ _)) => true
      | _ => false
  | .error _ => false
#guard match admitUnary with
  | .ok function =>
      match function.body with
      | .block (.return_ expression) =>
          match expression.expression with
          | .unary operator _ => operator == "-"
          | _ => false
      | _ => false
  | .error _ => false
#guard match admitLogical with
  | .ok function =>
      match function.body with
      | .block (.return_ expression) =>
          match expression.expression with
          | .logical operator _ _ => operator == "&&"
          | _ => false
      | _ => false
  | .error _ => false
#guard match admitBinary with
  | .ok function =>
      match function.body with
      | .block (.return_ expression) => match expression.expression with
        | .binary _ left right =>
          left.sourceType == intType && left.type == intType &&
            right.sourceType == intType && right.type == intType
        | _ => false
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

-- Compound statements retain every boundary, including empty and singleton blocks.
#guard (parseCallableStatement .lp64 [] [] intType
  (object [("kind", text "CompoundStmt"), ("inner", .array [])])).toOption == some (.block .skip)
#guard (parseCallableStatement .lp64 [] [] intType
  (body (body (object [("kind", text "NullStmt")])))).toOption == some (.block (.block .skip))
#guard match admitFor with
  | .ok function => match function.body with
    | .block (.sequence (.forLoop (.assign _ _) _ (.expression _) (.block _)) (.return_ _)) => true
    | _ => false
  | .error _ => false
#guard match admitForContinue with
  | .ok function => match function.body with
    | .block (.sequence (.forLoop _ _ _ (.block (.block .continue_))) (.return_ _)) => true
    | _ => false
  | .error _ => false
-- Retaining control nodes does not admit declarations, even in nested blocks.
#guard match parseCallableStatement .lp64 [] [] intType
    (body (object [("kind", text "DeclStmt")])) with
  | .error message => message == "callable: unsupported statement DeclStmt"
  | .ok _ => false

end LeanModels.Cpp.CallableTests
