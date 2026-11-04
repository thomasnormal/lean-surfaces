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
  match type with
  | .lvalueReference referent =>
      let _ ← requireIntegralType "reference referent" referent
      if row.isConstexpr then
        throw "automatic declaration: constexpr references are outside the local profile"
  | _ =>
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

private def initializerType (rows : List CppInitializerExpressionType) (raw : Raw) :
    Except String CppTypeEvidence := do
  let occurrence ← evidenceHandle raw "id"
  let kind ← evidenceText raw "kind"
  let matchingRows := rows.filter (·.occurrence == occurrence)
  let row :: rest := matchingRows
    | throw "automatic declaration: missing initializer subexpression type"
  unless row.kind == kind && rest.all (fun other => other == row) do
    throw "automatic declaration: conflicting initializer subexpression type"
  pure row.type

private def integralFormat (profile : TargetProfile) (type : CppTypeEvidence) :
    Except String IntegralFormat := do
  let integer ← requireIntegralType "subexpression type" type
  match profile.format integer with
  | .ok format => pure format
  | .error _ => throw "automatic declaration: subexpression type unavailable in target profile"

private partial def parseExpression (profile : TargetProfile)
    (available : List FrontendHandle)
    (expressionRows : List CppBinaryExpressionEvidence)
    (types : List CppInitializerExpressionType)
    (raw : Raw) (sourceExpected typeExpected : Option CppTypeEvidence) :
    Except String Expression := do
  let kind ← evidenceText raw "kind"
  let actual ← if types.isEmpty then pure none else some <$> initializerType types raw
  if let some type := actual then
    let _ ← requireIntegralType "subexpression type" type
    if let some expected := typeExpected then
      unless type == expected do
        throw "automatic declaration: subexpression result disagrees with typed evidence"
  match kind with
  | "IntegerLiteral" =>
      parseLiteral profile raw (actual.orElse (fun _ => sourceExpected))
        (actual.orElse (fun _ => typeExpected))
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
      if let some destination := actual then
        let childType ← initializerType types child
        let operand ← parseExpression profile available expressionRows types child
          (some childType) (some childType)
        let format ← integralFormat profile destination
        pure (.convert format operand)
      else
        unless ["LValueToRValue", "NoOp"].contains castKind do
          throw "automatic declaration: integral cast requires subexpression type evidence"
        parseExpression profile available expressionRows types child sourceExpected typeExpected
  | "ParenExpr" | "ConstantExpr" | "ExprWithCleanups" | "MaterializeTemporaryExpr" |
      "CXXConstructExpr" | "ParenListExpr" =>
      let children ← rawChildren raw
      let [child] := children
        | throw "automatic declaration: expression wrapper requires one child"
      parseExpression profile available expressionRows types child
        (actual.orElse (fun _ => sourceExpected)) (actual.orElse (fun _ => typeExpected))
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
        if types.isEmpty then
          unless operand.sourceType == operand.type do
            throw "automatic declaration: implicit operand conversion requires subexpression type evidence"
      let left ← parseExpression profile available expressionRows types leftRaw
        (some leftEvidence.sourceType) (some leftEvidence.type)
      let right ← parseExpression profile available expressionRows types rightRaw
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
      let some resultType := actual
        | throw "automatic declaration: unary initializer requires subexpression type evidence"
      let operandType ← initializerType types child
      let operandInteger ← requireIntegralType "unary operand type" operandType
      let resultInteger ← requireIntegralType "unary result type" resultType
      if operation == .logicalNot then
        unless operandInteger == .boolean && resultInteger == .boolean do
          throw "automatic declaration: logical negation requires boolean operand/result"
      else
        let promoted ← match integralPromotion profile operandInteger with
          | .ok type => pure type
          | .error _ => throw "automatic declaration: unary promotion is unresolved"
        unless operandInteger == promoted && resultInteger == promoted do
          throw "automatic declaration: unary operand/result disagrees with promotion"
      let operand ← parseExpression profile available expressionRows types child
        (some operandType) (some operandType)
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
  let sourceType := if evidence.expressionTypes.isEmpty then evidence.sourceType else evidence.type
  match row.initStyle with
  | .call | .parenList =>
      let value ← if evidence.kind == "InitListExpr" then
          let children ← rawChildren initializer
          match children with
          | [child] => pure child
          | _ => throw "automatic declaration: direct scalar initialization requires one element"
        else pure initializer
      let expression ← parseExpression profile (row.occurrence :: available)
        expressionRows evidence.expressionTypes value (some evidence.sourceType) (some evidence.type)
      pure (.declare row.occurrence destinationType sourceType expression)
  | .c | .list =>
      if evidence.kind == "InitListExpr" then
        let children ← rawChildren initializer
        match children with
        | [] => pure (.zeroDeclare row.occurrence destinationType)
        | [child] =>
            let expression ← parseExpression profile (row.occurrence :: available)
              expressionRows evidence.expressionTypes child (some evidence.sourceType) (some evidence.type)
            pure (.declare row.occurrence destinationType sourceType expression)
        | _ => throw "automatic declaration: initializer list requires zero or one element"
      else if evidence.kind == "CXXScalarValueInitExpr" then
        let children ← rawChildren initializer
        unless children.isEmpty do
          throw "automatic declaration: scalar value initializer has children"
        pure (.zeroDeclare row.occurrence destinationType)
      else
        let expression ← parseExpression profile (row.occurrence :: available)
          expressionRows evidence.expressionTypes initializer (some evidence.sourceType) (some evidence.type)
        pure (.declare row.occurrence destinationType sourceType expression)

private def sequenceAll : List IntegralObjectFrame.Statement → IntegralObjectFrame.Statement
  | [] => .skip
  | statement :: rest => rest.foldl (fun accumulated next => .sequence accumulated next) statement

private def declarationReferent : CppTypeEvidence → CppTypeEvidence
  | .lvalueReference referent => referent
  | type => type

private def referenceCompatible (source destination : CppTypeEvidence) : Except String Unit :=
  match IntegralObjectStore.validateReferenceTypes source destination with
  | .ok _ => pure ()
  | .error _ => throw "automatic declaration: incompatible reference type or qualification"

private partial def referenceTarget (typeRows : List TypeEvidenceRow)
    (available : List FrontendHandle) (types : List CppInitializerExpressionType)
    (raw : Raw) : Except String (FrontendHandle × CppTypeEvidence × CppTypeEvidence) := do
  unless raw.text "valueCategory" == some "lvalue" do
    throw "automatic declaration: reference initializer is not an existing-object lvalue"
  let actual ← initializerType types raw
  let _ ← requireIntegralType "reference initializer type" actual
  let kind ← evidenceText raw "kind"
  match kind with
  | "DeclRefExpr" =>
      let referenced ← evidenceField raw "referencedDecl"
      unless ["VarDecl", "ParmVarDecl"].contains ((referenced.text "kind").getD "") do
        throw "automatic declaration: reference target is not a variable or parameter"
      let target ← evidenceHandle referenced "id"
      unless available.contains target do
        throw "automatic declaration: reference target is not in scope"
      let type ← typeRow? typeRows target
      unless declarationReferent type == actual do
        throw "automatic declaration: reference target type disagrees with initializer"
      pure (target, actual, actual)
  | "ParenExpr" | "InitListExpr" | "ImplicitCastExpr" =>
      if kind == "ImplicitCastExpr" then
        unless raw.text "castKind" == some "NoOp" do
          throw "automatic declaration: reference initializer cast is not qualification-only"
      let [child] ← rawChildren raw
        | throw "automatic declaration: reference wrapper requires one child"
      let (target, childType, sourceType) ← referenceTarget typeRows available types child
      if kind == "ImplicitCastExpr" then referenceCompatible childType actual
      else unless childType == actual do
        throw "automatic declaration: reference wrapper changes type"
      pure (target, actual, if kind == "InitListExpr" then actual else sourceType)
  | _ => throw s!"automatic declaration: unsupported reference initializer {kind}"

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
  if let .lvalueReference referent := type then
    let some initializerEvidence := evidence.initializer
      | throw "automatic declaration: reference requires an initializer"
    let [initializer] := values
      | throw "automatic declaration: reference initializer child is absent"
    unless initializer.text "id" == some initializerEvidence.occurrence.value &&
        initializer.text "kind" == some initializerEvidence.kind do
      throw "automatic declaration: reference initializer identity disagrees with evidence"
    let (target, actual, sourceType) ← referenceTarget typeRows available initializerEvidence.expressionTypes initializer
    unless actual == initializerEvidence.type && sourceType == initializerEvidence.sourceType do
      throw "automatic declaration: reference initializer type disagrees with evidence"
    referenceCompatible actual referent
    return (.reference declaration type target, declaration)
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
