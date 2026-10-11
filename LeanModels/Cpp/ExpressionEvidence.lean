import LeanModels.Cpp.TypeEvidence

namespace LeanModels.Cpp

structure CppExpressionOperandEvidence where
  occurrence : FrontendHandle
  kind : String
  type : CppTypeEvidence
  deriving Repr, BEq, Inhabited

structure CppBinaryExpressionEvidence where
  ordinal : Nat
  occurrence : FrontendHandle
  operator : String
  result : CppTypeEvidence
  operands : List CppExpressionOperandEvidence
  deriving Repr, BEq, Inhabited

private def parseExpressionOperand (raw : Raw) : Except String CppExpressionOperandEvidence := do
  return {
    occurrence := ← evidenceHandle raw "occurrence"
    kind := ← evidenceText raw "kind"
    type := ← parseCppTypeEvidence (← evidenceField raw "type")
  }

private def parseBinaryExpressionRow (ordinal : Nat) (raw : Raw) :
    Except String CppBinaryExpressionEvidence := do
  requireEvidenceText raw "expression_api" "Clang::BinaryOperator typed operand projection v1"
  unless (← evidenceText raw "kind") == "BinaryOperator" do
    throw "expression evidence kind is not BinaryOperator"
  let operands ← match ← evidenceField raw "operands" with
    | .array values => values.mapM parseExpressionOperand
    | _ => throw "expression evidence operands: expected array"
  if operands.length != 2 then
    throw "binary expression evidence requires exactly two operands"
  return {
    ordinal
    occurrence := ← evidenceHandle raw "occurrence"
    operator := ← evidenceText raw "operator"
    result := ← parseCppTypeEvidence (← evidenceField raw "result")
    operands
  }

def parseBinaryExpressionEvidenceRows (raw : Raw) :
    Except String (List CppBinaryExpressionEvidence) := do
  let values ← match raw with
    | .array values => .ok values
    | _ => .error "expression evidence: expected array"
  values.zipIdx.mapM fun (value, ordinal) => parseBinaryExpressionRow ordinal value

private partial def rawObjects : Raw → List Raw
  | raw@(.object fields) => raw :: fields.flatMap (fun (_, value) => rawObjects value)
  | .array values => values.flatMap rawObjects
  | _ => []

private def rawNode (ast : Raw) (handle : FrontendHandle) : Option Raw :=
  (rawObjects ast).find? fun raw => raw.text "id" == some handle.value

private def rawChildren (raw : Raw) : List Raw :=
  match raw.field "inner" with
  | some (.array values) => values
  | _ => []

private partial def knownTypeReferences (type : CppTypeEvidence)
    (declarations : List DeclarationEvidenceRow) : Bool :=
  match type with
  | .builtin _ => true
  | .pointer pointee | .lvalueReference pointee | .rvalueReference pointee =>
      knownTypeReferences pointee declarations
  | .qualified _ _ base => knownTypeReferences base declarations
  | .function result parameters _ =>
      knownTypeReferences result declarations &&
        parameters.all (fun parameter => knownTypeReferences parameter declarations)
  | .record declaration | .enumeration declaration =>
      declarations.any (fun row => row.id == declaration)

private def sameExpression (left right : CppBinaryExpressionEvidence) : Bool :=
  left.occurrence == right.occurrence && left.operator == right.operator &&
    left.result == right.result && left.operands == right.operands

def validateBinaryExpressionEvidence (probe : DeclarationProbe)
    (rows : List CppBinaryExpressionEvidence) : Except String Unit := do
  let rec validate (remaining : List CppBinaryExpressionEvidence)
      (seen : List CppBinaryExpressionEvidence) : Except String Unit := do
    match remaining with
    | [] => return
    | row :: rest =>
        let some node := rawNode probe.ast row.occurrence
          | throw "expression evidence occurrence is absent from AST"
        unless node.text "kind" == some "BinaryOperator" do
          throw "expression evidence occurrence is not a BinaryOperator"
        unless node.text "opcode" == some row.operator do
          throw "expression evidence operator disagrees with AST"
        let children := rawChildren node
        unless children.length == 2 do
          throw "binary AST node does not have exactly two children"
        for (child, operand) in children.zip row.operands do
          let some childId := child.text "id"
            | throw "binary AST child has no occurrence handle"
          unless childId == operand.occurrence.value do
            throw "expression operand order disagrees with AST"
          unless child.text "kind" == some operand.kind do
            throw "expression operand kind disagrees with AST"
          unless knownTypeReferences operand.type probe.declarations do
            throw "expression operand type refers to an absent declaration"
        unless knownTypeReferences row.result probe.declarations do
          throw "expression result type refers to an absent declaration"
        if seen.any (fun prior => prior.occurrence == row.occurrence) then
          unless seen.all (fun prior => prior.occurrence != row.occurrence || sameExpression prior row) do
            throw "conflicting repeated expression evidence"
        validate rest (row :: seen)
  validate rows []

def parseValidatedBinaryExpressionEvidence (probe : DeclarationProbe) :
    Except String (List CppBinaryExpressionEvidence) := do
  let metadata := probe.metadata
  requireEvidenceText metadata "expression_evidence_api"
    "Clang::BinaryOperator typed operand projection v1"
  let rows ← parseBinaryExpressionEvidenceRows (← evidenceField metadata "expression_evidence")
  validateBinaryExpressionEvidence probe rows
  return rows

end LeanModels.Cpp
