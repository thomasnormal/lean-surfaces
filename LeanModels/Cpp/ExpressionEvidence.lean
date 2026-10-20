import LeanModels.Cpp.TypeEvidence

namespace LeanModels.Cpp

structure CppExpressionTypeEvidence where
  occurrence : FrontendHandle
  kind : String
  type : CppTypeEvidence
  deriving Repr, BEq, Inhabited

def expressionTypeFor (rows : List CppExpressionTypeEvidence) (raw : Raw) :
    Except String CppTypeEvidence := do
  let occurrence ← evidenceHandle raw "id"
  let kind ← evidenceText raw "kind"
  let matchingRows := rows.filter (·.occurrence == occurrence)
  let row :: rest := matchingRows | throw "expression type: missing occurrence"
  unless row.kind == kind && rest.all (fun other => other == row) do
    throw "expression type: conflicting occurrence/kind/type"
  pure row.type

mutual
  private def expressionInnerNodes : Raw → List Raw
    | node@(.object fields) => node :: expressionInnerFields fields
    | _ => []

  private def expressionInnerFields : List (String × Raw) → List Raw
    | [] => []
    | (name, value) :: rest =>
        (if name == "inner" then
          match value with
          | .array values => expressionInnerValues values
          | _ => []
        else []) ++ expressionInnerFields rest

  private def expressionInnerValues : List Raw → List Raw
    | [] => []
    | value :: rest => expressionInnerNodes value ++ expressionInnerValues rest
end

/-- Restrict a validated module supplement to one callable body before parsing. -/
def expressionTypeRowsFor (raw : Raw) (rows : List CppExpressionTypeEvidence) :
    List CppExpressionTypeEvidence :=
  let ids := (expressionInnerNodes raw).filterMap (·.text "id")
  rows.filter (fun row => ids.contains row.occurrence.value)

structure CppExpressionOperandEvidence where
  occurrence : FrontendHandle
  kind : String
  sourceType : CppTypeEvidence
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
    sourceType := ← parseCppTypeEvidence (← evidenceField raw "source")
    type := ← parseCppTypeEvidence (← evidenceField raw "type")
  }

private def parseBinaryExpressionRow (ordinal : Nat) (raw : Raw) :
    Except String CppBinaryExpressionEvidence := do
  requireEvidenceText raw "expression_api" "Clang::BinaryOperator typed operand projection v2"
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

private def firstRawNodes (nodes : List Raw) : Std.HashMap String Raw :=
  nodes.foldl (init := {}) fun index node =>
    match node.text "id" with
    | none => index
    | some id => if index.contains id then index else index.insert id node

private def rawChildren (raw : Raw) : List Raw :=
  match raw.field "inner" with
  | some (.array values) => values
  | _ => []

private partial def knownTypeReferences (type : CppTypeEvidence)
    (declarations : List DeclarationEvidenceRow) : Bool :=
  match type with
  | .void | .builtin _ => true
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

private def builtinType? : CppTypeEvidence → Option CppIntType
  | .builtin type => some type
  | _ => none

/-- Lvalue-to-rvalue conversion removes nonvolatile source qualification before
promotion. Converted operand and result types are still required to be builtin. -/
private def builtinSourceType? : CppTypeEvidence → Option CppIntType
  | .builtin type => some type
  | .qualified _ false base => builtinSourceType? base
  | _ => none

private def integralOperator (operator : String) : Bool :=
  ["+", "-", "*", "/", "%", "&", "|", "^", "==", "!=", "<", "<=", ">", ">="].contains operator

private def shiftOperator (operator : String) : Bool :=
  operator == "<<" || operator == ">>"

private def comparisonOperator (operator : String) : Bool :=
  ["==", "!=", "<", "<=", ">", ">="].contains operator

def validateBinaryIntegralTyping (profile : TargetProfile)
    (row : CppBinaryExpressionEvidence) : Except String Unit := do
  let some leftOperand := row.operands[0]?
    | throw "integral expression typing requires a left operand"
  let some rightOperand := row.operands[1]?
    | throw "integral expression typing requires a right operand"
  let some leftSource := builtinSourceType? leftOperand.sourceType
    | throw "integral expression typing requires a builtin left source type"
  let some rightSource := builtinSourceType? rightOperand.sourceType
    | throw "integral expression typing requires a builtin right source type"
  let some leftType := builtinType? leftOperand.type
    | throw "integral expression typing requires a builtin left converted type"
  let some rightType := builtinType? rightOperand.type
    | throw "integral expression typing requires a builtin right converted type"
  let some resultType := builtinType? row.result
    | throw "integral expression typing requires a builtin result type"
  if integralOperator row.operator then
    let common ← match usualArithmeticType profile leftSource rightSource with
      | .ok type => pure type
      | .error _ => throw "integral expression usual arithmetic type is unresolved"
    unless leftType == common && rightType == common do
      throw "integral expression operands disagree with usual arithmetic type"
    let expectedResult := if comparisonOperator row.operator then .boolean else common
    unless resultType == expectedResult do
      throw "integral expression result disagrees with operator typing"
  else if shiftOperator row.operator then
    let expectedLeft ← match integralPromotion profile leftSource with
      | .ok type => pure type
      | .error _ => throw "integral shift left promotion is unresolved"
    let expectedRight ← match integralPromotion profile rightSource with
      | .ok type => pure type
      | .error _ => throw "integral shift right promotion is unresolved"
    unless leftType == expectedLeft && rightType == expectedRight do
      throw "integral shift operands disagree with promotions"
    unless resultType == expectedLeft do
      throw "integral shift result disagrees with promoted left type"
  else
    throw "expression operator is outside integral promotion typing"

def validateBinaryExpressionEvidence (probe : DeclarationProbe)
    (rows : List CppBinaryExpressionEvidence) : Except String Unit := do
  -- Preserve the original all-object traversal and its first-occurrence rule,
  -- while constructing that view once rather than once per evidence row.
  let nodes := firstRawNodes (rawObjects probe.ast)
  let rec validate (remaining : List CppBinaryExpressionEvidence)
      (seen : List CppBinaryExpressionEvidence) : Except String Unit := do
    match remaining with
    | [] => return
    | row :: rest =>
        let some node := nodes[row.occurrence.value]?
          | throw "expression evidence occurrence is absent from AST"
        unless node.text "kind" == some "BinaryOperator" ||
            node.text "kind" == some "CompoundAssignOperator" do
          throw "expression evidence occurrence is not a BinaryOperator or CompoundAssignOperator"
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
    "Clang::BinaryOperator typed operand projection v2"
  let rows ← parseBinaryExpressionEvidenceRows (← evidenceField metadata "expression_evidence")
  validateBinaryExpressionEvidence probe rows
  return rows

/-- `none` denotes a legacy capture; `some []` still requires types at every use. -/
def parseValidatedExpressionTypeEvidence (probe : DeclarationProbe) :
    Except String (Option (List CppExpressionTypeEvidence)) := do
  match probe.metadata.field "expression_types_api", probe.metadata.field "expression_types" with
  | none, none => pure none
  | some (.string "Clang::Expr type projection v1"), some (.array values) =>
      let rows ← values.mapM fun value => return ({
        occurrence := ← evidenceHandle value "occurrence"
        kind := ← evidenceText value "kind"
        type := ← parseCppTypeEvidence (← evidenceField value "type")
      } : CppExpressionTypeEvidence)
      let nodes := (expressionInnerNodes probe.ast).foldl (init :=
          ({} : Std.HashMap String (List (Option String)))) fun index node =>
        match node.text "id" with
        | none => index
        | some id => index.insert id (node.text "kind" :: index[id]?.getD [])
      let byOccurrence := rows.foldl (init :=
          ({} : Std.HashMap String (List CppExpressionTypeEvidence))) fun index row =>
        let id := row.occurrence.value
        index.insert id (row :: index[id]?.getD [])
      for row in rows do
        let matchingKinds := nodes[row.occurrence.value]?.getD []
        unless !matchingKinds.isEmpty && matchingKinds.all (· == some row.kind) do
          throw "expression type: occurrence/kind disagrees with AST inner tree"
        unless row.type.referencesKnown probe.declarations do
          throw "expression type: absent type declaration"
        unless (byOccurrence[row.occurrence.value]?.getD []).all (· == row) do
          throw "expression type: conflicting repeated row"
      pure (some rows)
  | _, _ => throw "expression type: missing or unsupported supplement"

end LeanModels.Cpp
