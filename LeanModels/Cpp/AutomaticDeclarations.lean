import LeanModels.Cpp.IntegralObjectFrame
import LeanModels.Cpp.VariableEvidence
import LeanModels.Cpp.ExpressionEvidence

namespace LeanModels.Cpp

open IntegralObjectFrame

/-- The result of admitting one Clang `DeclStmt` into the object-frame shell. -/
structure AdmittedAutomaticDeclStmt where
  statement : IntegralObjectFrame.Statement
  declarations : List FrontendHandle
  deriving Repr, BEq, Inhabited

namespace AdmittedAutomaticDeclStmt

private def rawChildren (raw : Raw) : Except String (List Raw) :=
  match raw.field "inner" with
  | none => .ok []
  | some (.array values) => .ok values
  | some _ => .error "automatic declaration: malformed inner field"

private def atInnerPath : Raw → List Nat → Option Raw
  | raw, [] => some raw
  | raw, index :: rest => do
      let values ← raw.field "inner" |>.bind Raw.array?
      let child ← values[index]?
      atInnerPath child rest

private def ancillary (raw : Raw) : Bool :=
  (raw.text "kind").any (fun kind =>
    kind.endsWith "Attr" || ["FullComment", "TemplateArgument", "BindingDecl"].contains kind)

private def valueChildren (raw : Raw) : Except String (List Raw) :=
  return (← rawChildren raw).filter (fun child => !ancillary child)

private def variableRow? (rows : List CppVariableEvidence)
    (declaration : FrontendHandle) : Except String CppVariableEvidence :=
  match rows.filter (fun row => row.occurrence == declaration) with
  | [] => .error "automatic declaration: missing variable evidence"
  | row :: rest =>
      if rest.any (fun other => other != row) then
        .error "automatic declaration: conflicting variable evidence"
      else .ok row

private def typeRow? (rows : List TypeEvidenceRow)
    (declaration : FrontendHandle) : Except String CppTypeEvidence :=
  match rows.filter (fun row => row.occurrence == declaration) with
  | [] => .error "automatic declaration: missing structured variable type"
  | row :: rest =>
      if rest.any (fun other => other != row) then
        .error "automatic declaration: conflicting structured variable type"
      else .ok row.type

private def integralType? : CppTypeEvidence → Option CppIntType
  | .builtin type => some type
  | .qualified _ isVolatile base =>
      if isVolatile then none else integralType? base
  | _ => none

private def requireIntegralType (context : String) (type : CppTypeEvidence) : Except String CppIntType :=
  match integralType? type with
  | some result => .ok result
  | none => .error s!"automatic declaration: {context} is not a nonvolatile integral type"

private def isConstType : CppTypeEvidence → Bool
  | .qualified isConst isVolatile base => isConst && !isVolatile && (integralType? base).isSome
  | _ => false

private def allowedStorage : CppVariableStorageClass → Bool
  | .none_ | .auto_ | .register_ => true
  | .extern_ | .static_ | .privateExtern => false

private def validateVariable (row : CppVariableEvidence) (type : CppTypeEvidence) :
    Except String Unit := do
  unless row.kind == "VarDecl" && row.isLocal && row.localOrParameter do
    throw "automatic declaration: child is not an ordinary local VarDecl"
  unless row.storageDuration == .automatic && row.tls == .none_ && allowedStorage row.storageClass do
    throw "automatic declaration: storage is not automatic"
  unless row.attributeCount == 0 do
    throw "automatic declaration: attributes are outside the local profile"
  let _ ← requireIntegralType "object type" type
  if row.isConstexpr && !isConstType type then
    throw "automatic declaration: constexpr object is not const-qualified"
  pure ()

private def binaryOperation? : String → Option IntegralBinary
  | "+" => some .add
  | "-" => some .subtract
  | "*" => some .multiply
  | "/" => some .divide
  | "%" => some .remainder
  | "<<" => some .shiftLeft
  | ">>" => some .shiftRight
  | "&" => some .bitAnd
  | "|" => some .bitOr
  | "^" => some .bitXor
  | "==" => some .equal
  | "!=" => some .notEqual
  | "<" => some .less
  | "<=" => some .lessEqual
  | ">" => some .greater
  | ">=" => some .greaterEqual
  | _ => none

private def unaryOperation? : String → Option IntegralUnary
  | "+" => some .plus
  | "-" => some .negate
  | "~" => some .complement
  | "!" => some .logicalNot
  | _ => none

private def parseLiteral (profile : TargetProfile) (raw : Raw)
    (sourceExpected typeExpected : Option CppTypeEvidence) : Except String Expression := do
  let sourceType := sourceExpected.orElse (fun _ => typeExpected)
  let some sourceType := sourceType
    | throw "automatic declaration: literal lacks source type evidence"
  let sourceInteger ← requireIntegralType "literal source type" sourceType
  let _ ← match typeExpected with
    | some type => requireIntegralType "literal result type" type
    | none => pure sourceInteger
  let some value := (← evidenceText raw "value").toInt?
    | throw "automatic declaration: literal value is not a decimal integer"
  let format ← match profile.format sourceInteger with
    | .ok format => pure format
    | .error _ => throw "automatic declaration: literal type is unavailable in target profile"
  pure (.literal {format, value})

private partial def parseExpression (profile : TargetProfile)
    (available : List FrontendHandle)
    (expressionRows : List CppBinaryExpressionEvidence)
    (raw : Raw) (sourceExpected typeExpected : Option CppTypeEvidence) :
    Except String Expression := do
  let kind ← evidenceText raw "kind"
  match kind with
  | "IntegerLiteral" => parseLiteral profile raw sourceExpected typeExpected
  | "DeclRefExpr" =>
      let reference ← evidenceField raw "referencedDecl"
      let declaration ← evidenceHandle reference "id"
      unless available.contains declaration do
        throw "automatic declaration: initializer references an unavailable declaration"
      let _ ← match sourceExpected with
        | some type => requireIntegralType "reference source type" type
        | none => pure .int
      let _ ← match typeExpected with
        | some type => requireIntegralType "reference result type" type
        | none => pure .int
      pure (.read declaration)
  | "ImplicitCastExpr" =>
      let castKind ← evidenceText raw "castKind"
      unless ["LValueToRValue", "NoOp", "IntegralCast", "IntegralToBoolean"].contains castKind do
        throw s!"automatic declaration: unsupported initializer cast {castKind}"
      let children ← rawChildren raw
      let [child] := children
        | throw "automatic declaration: initializer cast requires one child"
      let childExpected := if castKind == "IntegralCast" || castKind == "IntegralToBoolean"
        then sourceExpected else sourceExpected
      parseExpression profile available expressionRows child childExpected
        (if castKind == "IntegralCast" || castKind == "IntegralToBoolean"
          then sourceExpected else typeExpected)
  | "ParenExpr" | "ConstantExpr" | "ExprWithCleanups" | "MaterializeTemporaryExpr" |
      "CXXConstructExpr" | "ParenListExpr" =>
      let children ← rawChildren raw
      let [child] := children
        | throw "automatic declaration: expression wrapper requires one child"
      parseExpression profile available expressionRows child sourceExpected typeExpected
  | "BinaryOperator" =>
      let occurrence ← evidenceHandle raw "id"
      let some evidence := expressionRows.find? (fun row => row.occurrence == occurrence)
        | throw "automatic declaration: binary initializer lacks typed evidence"
      let some operation := binaryOperation? evidence.operator
        | throw s!"automatic declaration: unsupported initializer operator {evidence.operator}"
      let _ ← validateBinaryIntegralTyping profile evidence
      let children ← rawChildren raw
      let [leftRaw, rightRaw] := children
        | throw "automatic declaration: binary initializer requires two children"
      let [leftEvidence, rightEvidence] := evidence.operands
        | throw "automatic declaration: binary initializer evidence requires two operands"
      for (child, operand) in [(leftRaw, leftEvidence), (rightRaw, rightEvidence)] do
        unless child.text "id" == some operand.occurrence.value &&
            child.text "kind" == some operand.kind do
          throw "automatic declaration: binary initializer child disagrees with evidence"
        unless operand.sourceType == operand.type do
          throw "automatic declaration: implicit operand conversion is outside the frame expression fragment"
      let left ← parseExpression profile available expressionRows leftRaw
        (some leftEvidence.sourceType) (some leftEvidence.type)
      let right ← parseExpression profile available expressionRows rightRaw
        (some rightEvidence.sourceType) (some rightEvidence.type)
      if let some expected := typeExpected then
        unless expected == evidence.result do
          throw "automatic declaration: binary initializer result disagrees with evidence"
      pure (.binary operation left right)
  | "UnaryOperator" =>
      let operator ← evidenceText raw "opcode"
      let some operation := unaryOperation? operator
        | throw s!"automatic declaration: unsupported initializer unary operator {operator}"
      let children ← rawChildren raw
      let [child] := children
        | throw "automatic declaration: unary initializer requires one child"
      let _ ← match sourceExpected with
        | some type => requireIntegralType "unary initializer source type" type
        | none => pure .int
      let _ ← match typeExpected with
        | some type => requireIntegralType "unary initializer result type" type
        | none => pure .int
      let operand ← parseExpression profile available expressionRows child sourceExpected typeExpected
      pure (.unary operation operand)
  | _ => throw s!"automatic declaration: unsupported initializer expression {kind}"

private def parseInitializer (profile : TargetProfile)
    (available : List FrontendHandle)
    (expressionRows : List CppBinaryExpressionEvidence)
    (row : CppVariableEvidence) (destinationType : CppTypeEvidence)
    (initializer : Raw) : Except String IntegralObjectFrame.Statement := do
  let some evidence := row.initializer
    | throw "automatic declaration: initializer evidence is absent"
  unless initializer.text "id" == some evidence.occurrence.value &&
      initializer.text "kind" == some evidence.kind do
    throw "automatic declaration: initializer identity disagrees with evidence"
  let _ ← requireIntegralType "initializer source type" evidence.sourceType
  let _ ← requireIntegralType "initializer result type" evidence.type
  match row.initStyle with
  | .call | .parenList =>
      let value ← if evidence.kind == "InitListExpr" then
          let children ← rawChildren initializer
          match children with
          | [child] => pure child
          | _ => throw "automatic declaration: direct scalar initialization requires one element"
        else pure initializer
      let expression ← parseExpression profile (row.occurrence :: available)
        expressionRows value (some evidence.sourceType) (some evidence.type)
      pure (.declare row.occurrence destinationType evidence.sourceType expression)
  | .c | .list =>
      if evidence.kind == "InitListExpr" then
        let children ← rawChildren initializer
        match children with
        | [] => pure (.zeroDeclare row.occurrence destinationType)
        | [child] =>
            let expression ← parseExpression profile (row.occurrence :: available)
              expressionRows child (some evidence.sourceType) (some evidence.type)
            pure (.declare row.occurrence destinationType evidence.sourceType expression)
        | _ => throw "automatic declaration: initializer list requires zero or one element"
      else if evidence.kind == "CXXScalarValueInitExpr" then
        let children ← rawChildren initializer
        unless children.isEmpty do
          throw "automatic declaration: scalar value initializer has children"
        pure (.zeroDeclare row.occurrence destinationType)
      else
        let expression ← parseExpression profile (row.occurrence :: available)
          expressionRows initializer (some evidence.sourceType) (some evidence.type)
        pure (.declare row.occurrence destinationType evidence.sourceType expression)

private def sequenceAll : List IntegralObjectFrame.Statement → IntegralObjectFrame.Statement
  | [] => .skip
  | statement :: rest => rest.foldl (fun accumulated next => .sequence accumulated next) statement

private def admitChild (profile : TargetProfile)
    (typeRows : List TypeEvidenceRow) (variableRows : List CppVariableEvidence)
    (expressionRows : List CppBinaryExpressionEvidence)
    (available : List FrontendHandle) (child : Raw) :
    Except String (IntegralObjectFrame.Statement × FrontendHandle) := do
  unless child.text "kind" == some "VarDecl" do
    throw "automatic declaration: DeclStmt contains a non-VarDecl child"
  let declaration ← evidenceHandle child "id"
  let evidence ← variableRow? variableRows declaration
  let type ← typeRow? typeRows declaration
  validateVariable evidence type
  let values ← valueChildren child
  let statement ← match evidence.initializer with
    | none =>
        unless evidence.initStyle == .c do
          throw "automatic declaration: no initializer must use C initialization style"
        unless child.field "init" == none && values.isEmpty do
          throw "automatic declaration: absent initializer disagrees with AST"
        pure (.defaultDeclare declaration type)
    | some _ =>
        let [initializer] := values
          | throw "automatic declaration: initializer child is absent"
        parseInitializer profile available expressionRows evidence type initializer
  pure (statement, declaration)

def admit (probe : DeclarationProbe) (typeRows : List TypeEvidenceRow)
    (variableRows : List CppVariableEvidence)
    (expressionRows : List CppBinaryExpressionEvidence)
    (profile : TargetProfile) (available : List FrontendHandle) (path : List Nat) :
    Except String AdmittedAutomaticDeclStmt := do
  unless profile.valid do throw "automatic declaration: invalid target profile"
  let some statementRaw := atInnerPath probe.ast path
    | throw "automatic declaration: AST path is absent"
  unless statementRaw.text "kind" == some "DeclStmt" do
    throw "automatic declaration: AST path is not a DeclStmt"
  let children ← rawChildren statementRaw
  unless !children.isEmpty do
    throw "automatic declaration: declaration statement is empty"
  let rec loop (remaining : List Raw) (scope : List FrontendHandle)
      (statements : List IntegralObjectFrame.Statement) (declarations : List FrontendHandle) :
      Except String AdmittedAutomaticDeclStmt :=
    match remaining with
    | [] => pure {statement := sequenceAll statements, declarations := declarations.reverse}
    | child :: rest => do
        let (statement, declaration) ← admitChild profile typeRows variableRows
          expressionRows (scope ++ available) child
        loop rest (declaration :: scope) (statements ++ [statement]) (declaration :: declarations)
  loop children [] [] []

def admitFromProbe (probe : DeclarationProbe) (profile : TargetProfile)
    (available : List FrontendHandle) (path : List Nat) :
    Except String AdmittedAutomaticDeclStmt := do
  let typeRows ← parseValidatedTypeEvidence probe
  let variableRows ← parseValidatedVariableEvidence probe
  let expressionRows ← parseValidatedBinaryExpressionEvidence probe
  admit probe typeRows variableRows expressionRows profile available path

end AdmittedAutomaticDeclStmt

end LeanModels.Cpp
