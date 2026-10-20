import LeanModels.Cpp.ExpressionEvidence

namespace LeanModels.Cpp.ExpressionEvidenceTests

open LeanModels.Cpp

private def text (value : String) : Raw := .string value
private def object (fields : List (String × Raw)) : Raw := .object fields
private def builtin (name : String) : Raw := object [("kind", text "builtin"), ("name", text name)]
private def operand (identifier kind : String) : Raw := object [
  ("occurrence", text identifier), ("kind", text kind),
  ("source", builtin "int"), ("type", builtin "int")]
private def narrowOperand (identifier : String) : Raw := object [
  ("occurrence", text identifier), ("kind", text "IntegerLiteral"),
  ("source", builtin "short"), ("type", builtin "int")]
private def expression (identifier operator : String) : Raw := object [
  ("expression_api", text "Clang::BinaryOperator typed operand projection v2"),
  ("occurrence", text identifier), ("kind", text "BinaryOperator"),
  ("operator", text operator), ("result", builtin "int"),
  ("operands", .array [operand "0x2" "IntegerLiteral", operand "0x3" "IntegerLiteral"])]
private def narrowExpression : Raw := object [
  ("expression_api", text "Clang::BinaryOperator typed operand projection v2"),
  ("occurrence", text "0x4"), ("kind", text "BinaryOperator"),
  ("operator", text "+"), ("result", builtin "int"),
  ("operands", .array [narrowOperand "0x2", narrowOperand "0x3"])]
private def ast : Raw := object [
  ("id", text "0x1"), ("kind", text "TranslationUnitDecl"),
  ("inner", .array [object [
    ("id", text "0x4"), ("kind", text "BinaryOperator"), ("opcode", text "+"),
    ("inner", .array [
      object [("id", text "0x2"), ("kind", text "IntegerLiteral")],
      object [("id", text "0x3"), ("kind", text "IntegerLiteral")]])]])]
private def probe : DeclarationProbe := {
  ast
  metadata := object []
  declarations := []
}
private def metadata : DeclarationProbe := {
  probe with metadata := object [
    ("expression_evidence_api",
      text "Clang::BinaryOperator typed operand projection v2"),
    ("expression_evidence", .array [expression "0x4" "+"])]
}
private def wrongMetadata : DeclarationProbe := {
  probe with metadata := object [
    ("expression_evidence_api",
      text "Clang::BinaryOperator typed operand projection v2"),
    ("expression_evidence", .array [expression "0x4" "*"])]
}

private def compoundMetadata (kind : String) : DeclarationProbe := {
  metadata with
  ast := object [("id", text "0x1"), ("kind", text "TranslationUnitDecl"),
    ("inner", .array [object [
      ("id", text "0x4"), ("kind", text kind), ("opcode", text "+="),
      ("inner", .array [
        object [("id", text "0x2"), ("kind", text "IntegerLiteral")],
        object [("id", text "0x3"), ("kind", text "IntegerLiteral")]])]])]
  metadata := object [
    ("expression_evidence_api", text "Clang::BinaryOperator typed operand projection v2"),
    ("expression_evidence", .array [expression "0x4" "+="])]
}

def rowsParse : Bool :=
  match parseBinaryExpressionEvidenceRows (.array [expression "0x4" "+"]) with
  | .ok rows => rows.length == 1
  | .error _ => false

def validates : Bool :=
  match parseValidatedBinaryExpressionEvidence metadata with
  | .ok rows => rows.length == 1
  | .error _ => false

def refusesWrongOperator : Bool :=
  match parseValidatedBinaryExpressionEvidence wrongMetadata with
  | .ok _ => false
  | .error _ => true

def promotionChecks : Bool :=
  match parseBinaryExpressionEvidenceRows (.array [narrowExpression]) with
  | .ok [row] =>
      match validateBinaryIntegralTyping TargetProfile.lp64 row with
      | .ok _ => true
      | .error _ => false
  | _ => false

#guard rowsParse
#guard validates
#guard refusesWrongOperator
#guard promotionChecks
#guard (parseValidatedBinaryExpressionEvidence
  (compoundMetadata "CompoundAssignOperator")).isOk
#guard (parseValidatedBinaryExpressionEvidence (compoundMetadata "UnaryOperator")) matches .error _

-- The indexed validator keeps the all-object, first-occurrence lookup contract.
-- A later full node must never repair an earlier stub with the same handle.
private def binaryNode : Raw :=
  (((ast.field "inner").bind Raw.array?).getD []).headD .null
private def binaryStub : Raw := object [
  ("id", text "0x4"), ("kind", text "DeclRefExpr")]
#guard (parseValidatedBinaryExpressionEvidence {metadata with
  ast := object [("payload", binaryNode)]}).isOk
#guard match parseValidatedBinaryExpressionEvidence {metadata with
  ast := object [("referencedDecl", binaryStub), ("inner", .array [binaryNode])]} with
  | .error error => error == "expression evidence occurrence is not a BinaryOperator or CompoundAssignOperator"
  | .ok _ => false
#guard (parseValidatedBinaryExpressionEvidence {metadata with
  ast := object [("inner", .array [binaryNode]), ("referencedDecl", binaryStub)]}).isOk

private def expressionTypeRow (id kind : String) (type : Raw) : Raw := object [
  ("occurrence", text id), ("kind", text kind), ("type", type)]

private def typedProbe (rows : List Raw) : DeclarationProbe := {
  probe with metadata := object [
    ("expression_types_api", text "Clang::Expr type projection v1"),
    ("expression_types", .array rows)]
}

private def literalType := expressionTypeRow "0x2" "IntegerLiteral" (builtin "int")

-- A missing supplement is legacy; a present-empty supplement is still strict.
#guard (parseValidatedExpressionTypeEvidence probe).toOption == some none
#guard (parseValidatedExpressionTypeEvidence (typedProbe [])).toOption == some (some [])
#guard (parseValidatedExpressionTypeEvidence (typedProbe [literalType, literalType])).isOk
#guard match parseValidatedExpressionTypeEvidence (typedProbe [literalType]) with
  | .ok (some rows) =>
      (expressionTypeFor rows (object [("id", text "0x2"),
        ("kind", text "IntegerLiteral")])).toOption == some (.builtin .int)
  | _ => false
#guard (expressionTypeFor [] (object [("id", text "0x2"),
  ("kind", text "IntegerLiteral")])) matches .error _
#guard (parseValidatedExpressionTypeEvidence {probe with metadata := object [
  ("expression_types_api", text "Clang::Expr type projection v1")]} ) matches .error _
#guard (parseValidatedExpressionTypeEvidence {probe with metadata := object [
  ("expression_types", .array [])]} ) matches .error _
#guard (parseValidatedExpressionTypeEvidence {probe with metadata := object [
  ("expression_types_api", text "future"), ("expression_types", .array [])]} ) matches .error _
#guard (parseValidatedExpressionTypeEvidence (typedProbe [
  expressionTypeRow "0x2" "DeclRefExpr" (builtin "int")])) matches .error _
#guard (parseValidatedExpressionTypeEvidence (typedProbe [literalType,
  expressionTypeRow "0x2" "IntegerLiteral" (builtin "long")])) matches .error _
#guard (parseValidatedExpressionTypeEvidence (typedProbe [
  expressionTypeRow "0x2" "IntegerLiteral" (object [
    ("kind", text "record"), ("declaration", text "0x99")])])) matches .error _
-- A reference stub outside inner is not an occurrence witness.
#guard (parseValidatedExpressionTypeEvidence {
  typedProbe [expressionTypeRow "0x99" "IntegerLiteral" (builtin "int")] with
  ast := object [("referencedDecl", object [("id", text "0x99"),
    ("kind", text "IntegerLiteral")])]} ) matches .error _
-- Every repeated AST occurrence must agree on kind.
#guard (parseValidatedExpressionTypeEvidence {
  typedProbe [literalType] with
  ast := object [("inner", .array [
    object [("id", text "0x2"), ("kind", text "IntegerLiteral")],
    object [("id", text "0x2"), ("kind", text "DeclRefExpr")]])]} ) matches .error _

#guard (expressionTypeFor [
  ⟨⟨"0x2"⟩, "IntegerLiteral", .builtin .int⟩,
  ⟨⟨"0x2"⟩, "IntegerLiteral", .builtin .long⟩]
  (object [("id", text "0x2"), ("kind", text "IntegerLiteral")])) matches .error _

end LeanModels.Cpp.ExpressionEvidenceTests
