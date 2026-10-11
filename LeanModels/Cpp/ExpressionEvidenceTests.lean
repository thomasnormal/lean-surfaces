import LeanModels.Cpp.ExpressionEvidence

namespace LeanModels.Cpp.ExpressionEvidenceTests

open LeanModels.Cpp

private def text (value : String) : Raw := .string value
private def object (fields : List (String × Raw)) : Raw := .object fields
private def builtin (name : String) : Raw := object [("kind", text "builtin"), ("name", text name)]
private def operand (identifier kind : String) : Raw := object [
  ("occurrence", text identifier), ("kind", text kind), ("type", builtin "int")]
private def expression (identifier operator : String) : Raw := object [
  ("expression_api", text "Clang::BinaryOperator typed operand projection v1"),
  ("occurrence", text identifier), ("kind", text "BinaryOperator"),
  ("operator", text operator), ("result", builtin "int"),
  ("operands", .array [operand "0x2" "IntegerLiteral", operand "0x3" "IntegerLiteral"])]
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
      text "Clang::BinaryOperator typed operand projection v1"),
    ("expression_evidence", .array [expression "0x4" "+"])]
}
private def wrongMetadata : DeclarationProbe := {
  probe with metadata := object [
    ("expression_evidence_api",
      text "Clang::BinaryOperator typed operand projection v1"),
    ("expression_evidence", .array [expression "0x4" "*"])]
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

#guard rowsParse
#guard validates
#guard refusesWrongOperator

end LeanModels.Cpp.ExpressionEvidenceTests
