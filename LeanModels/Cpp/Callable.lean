import LeanModels.Cpp.LocalFunction
import LeanModels.Cpp.ExpressionEvidence

namespace LeanModels.Cpp

mutual
  inductive CallableExpression where
    | integer (value : Nat)
    | parameter (declaration : FrontendHandle)
    | unary (operator : String) (operand : TypedCallableExpression)
    | binary (operator : String) (left right : TypedCallableExpression)
    deriving Repr, BEq, Inhabited

  structure TypedCallableExpression where
    expression : CallableExpression
    sourceType : CppTypeEvidence
    type : CppTypeEvidence
    deriving Repr, BEq, Inhabited

  inductive CallableStatement where
    | skip
    | expression (expression : TypedCallableExpression)
    | return_ (expression : TypedCallableExpression)
    | conditional (condition : TypedCallableExpression)
        (whenTrue whenFalse : CallableStatement)
    | whileLoop (condition : TypedCallableExpression) (body : CallableStatement)
    | sequence (first second : CallableStatement)
    deriving Repr, BEq, Inhabited
end

structure CallableParameter where
  declaration : FrontendHandle
  name : Option String
  type : CppTypeEvidence
  deriving Repr, BEq, Inhabited

structure CallableSignature where
  result : CppTypeEvidence
  parameters : List CppTypeEvidence
  variadic : Bool
  deriving Repr, BEq, Inhabited

structure CallableFunction where
  occurrence : Declaration
  signature : CallableSignature
  parameters : List CallableParameter
  body : CallableStatement
  deriving Repr, BEq, Inhabited

private def rawChildren (raw : Raw) : Except String (List Raw) :=
  match raw.field "inner" with
  | none => .ok []
  | some (.array values) => .ok values
  | some _ => .error "callable: malformed inner field"

private def rawId (raw : Raw) : Except String FrontendHandle :=
  evidenceHandle raw "id"

private def callableTypeRow (rows : List TypeEvidenceRow) (handle : FrontendHandle) :
    Except String TypeEvidenceRow :=
  match rows.filter (fun row => row.occurrence == handle) with
  | [] => .error "callable: missing structured type evidence"
  | row :: rest =>
      if rest.any (fun other => other != row) then
        .error "callable: conflicting structured type evidence"
      else .ok row

private def callableSignature (type : CppTypeEvidence) : Except String CallableSignature :=
  match type with
  | .function result parameters variadic =>
      if variadic then .error "callable: variadic functions are outside the body profile"
      else if !parameters.all (fun parameter => match parameter with
          | .builtin _ => true
          | _ => false) then
        .error "callable: non-integral parameter type is outside the body profile"
      else match result with
        | .builtin _ => .ok {result, parameters, variadic}
        | _ => .error "callable: non-integral result type is outside the body profile"
  | _ => .error "callable: declaration type is not a function type"

private def callableParameters (rawParameters : List Raw) (rows : List TypeEvidenceRow)
    (expected : List CppTypeEvidence) : Except String (List CallableParameter) := do
  if rawParameters.length != expected.length then
    throw "callable: parameter count disagrees with function type"
  let mut result : List CallableParameter := []
  for (raw, expectedType) in rawParameters.zip expected do
    unless raw.text "kind" == some "ParmVarDecl" do
      throw "callable: unsupported direct function child"
    let declaration ← rawId raw
    let row ← callableTypeRow rows declaration
    unless row.type == expectedType do
      throw "callable: parameter type disagrees with function type"
    result := result ++ [{declaration, name := raw.text "name", type := row.type}]
  pure result

private def parameterType? (parameters : List CallableParameter) (declaration : FrontendHandle) :
    Option CppTypeEvidence :=
  parameters.find? (fun parameter => parameter.declaration == declaration) |>.map (·.type)

private def integerLiteral (raw : Raw) (sourceExpected typeExpected : Option CppTypeEvidence) :
    Except String TypedCallableExpression := do
  let value ← evidenceText raw "value"
  let some value := value.toNat?
    | throw "callable: only nonnegative decimal integer literals are admitted"
  let type ← evidenceField raw "type"
  unless type.text "qualType" == some "int" do
    throw "callable: integer literal requires an exact int source type"
  unless sourceExpected.all (· == .builtin .int) do
    throw "callable: integer literal source type disagrees with expression evidence"
  unless typeExpected.all (· == .builtin .int) do
    throw "callable: integer literal requires an exact int result type"
  pure {expression := .integer value, sourceType := .builtin .int, type := .builtin .int}

partial def parseCallableExpression (profile : TargetProfile)
    (parameters : List CallableParameter)
    (expressionRows : List CppBinaryExpressionEvidence)
    (raw : Raw) (sourceExpected typeExpected : Option CppTypeEvidence) :
    Except String TypedCallableExpression := do
  let kind ← evidenceText raw "kind"
  match kind with
  | "IntegerLiteral" => integerLiteral raw sourceExpected typeExpected
  | "DeclRefExpr" =>
      let reference ← evidenceField raw "referencedDecl"
      let declaration ← rawId reference
      let some parameterType := parameterType? parameters declaration
        | throw "callable: expression references a non-parameter declaration"
      if sourceExpected.isSome && sourceExpected != some parameterType then
        throw "callable: parameter source type disagrees with expression evidence"
      if sourceExpected.isNone && typeExpected.isSome && typeExpected != some parameterType then
        throw "callable: parameter return conversion is outside the body profile"
      let type := typeExpected.getD parameterType
      pure {expression := .parameter declaration, sourceType := parameterType, type}
  | "ImplicitCastExpr" =>
      let castKind ← evidenceText raw "castKind"
      unless castKind == "LValueToRValue" || castKind == "NoOp" ||
          (castKind == "IntegralToBoolean" && sourceExpected.isNone && typeExpected.isNone) do
        throw s!"callable: unsupported implicit cast {castKind}"
      let children ← rawChildren raw
      match children with
      | [child] => parseCallableExpression profile parameters expressionRows child sourceExpected typeExpected
      | _ => throw "callable: implicit cast must have one child"
  | "ParenExpr" =>
      let children ← rawChildren raw
      match children with
      | [child] => parseCallableExpression profile parameters expressionRows child sourceExpected typeExpected
      | _ => throw "callable: parenthesized expression must have one child"
  | "BinaryOperator" =>
      let occurrence ← rawId raw
      let some row := expressionRows.find? (fun row => row.occurrence == occurrence)
        | throw "callable: binary body expression lacks typed evidence"
      validateBinaryIntegralTyping profile row
      unless raw.text "opcode" == some row.operator do
        throw "callable: binary body operator disagrees with typed evidence"
      if typeExpected.isSome && typeExpected != some row.result then
        throw "callable: binary result type disagrees with function return type"
      let children ← rawChildren raw
      match children, row.operands with
      | [leftRaw, rightRaw], [leftEvidence, rightEvidence] =>
          for (child, operand) in [(leftRaw, leftEvidence), (rightRaw, rightEvidence)] do
            unless child.text "id" == some operand.occurrence.value &&
                child.text "kind" == some operand.kind do
              throw "callable: binary operand disagrees with typed evidence"
          let left ← parseCallableExpression profile parameters expressionRows leftRaw
            (some leftEvidence.sourceType) (some leftEvidence.type)
          let right ← parseCallableExpression profile parameters expressionRows rightRaw
            (some rightEvidence.sourceType) (some rightEvidence.type)
          pure {
            expression := .binary row.operator left right
            sourceType := sourceExpected.getD row.result
            type := row.result
          }
      | _, _ => throw "callable: binary body expression requires two operands"
  | "UnaryOperator" =>
      let operator ← evidenceText raw "opcode"
      unless operator == "+" || operator == "-" || operator == "~" || operator == "!" do
        throw s!"callable: unsupported unary operator {operator}"
      let children ← rawChildren raw
      let [child] := children
        | throw "callable: unary body expression requires one operand"
      let operand ← parseCallableExpression profile parameters expressionRows child none none
      unless operator == "!" || operand.type != .builtin .boolean do
        throw "callable: unary integral promotion is outside the body profile"
      let type := if operator == "!" then .builtin .boolean else operand.type
      if typeExpected.isSome && typeExpected != some type then
        throw "callable: unary result type disagrees with expected type"
      pure {expression := .unary operator operand, sourceType := type, type}
  | _ => throw s!"callable: unsupported return expression {kind}"

partial def parseCallableStatement (profile : TargetProfile)
    (parameters : List CallableParameter)
    (expressionRows : List CppBinaryExpressionEvidence)
    (resultType : CppTypeEvidence) (statement : Raw) : Except String CallableStatement := do
  let kind ← evidenceText statement "kind"
  match kind with
  | "CompoundStmt" =>
      let children ← rawChildren statement
      match children with
      | [] => .ok .skip
      | first :: rest =>
          let first ← parseCallableStatement profile parameters expressionRows resultType first
          rest.foldlM (init := first) fun accumulated child => do
            let parsed ← parseCallableStatement profile parameters expressionRows resultType child
            pure (.sequence accumulated parsed)
  | "ReturnStmt" =>
      let values ← rawChildren statement
      let [value] := values
        | throw "callable: return statement requires exactly one expression"
      let expression ← parseCallableExpression profile parameters expressionRows value none
        (some resultType)
      unless expression.type == resultType do
        throw "callable: return expression type disagrees with function result"
      pure (.return_ expression)
  | "IfStmt" =>
      let children ← rawChildren statement
      match children with
      | [condition, whenTrue] | [condition, whenTrue, _] =>
          let condition ← parseCallableExpression profile parameters expressionRows condition none none
          let whenTrue ← parseCallableStatement profile parameters expressionRows resultType whenTrue
          let whenFalse ← match children with
            | [_, _, otherwise] =>
                parseCallableStatement profile parameters expressionRows resultType otherwise
            | _ => .ok .skip
          pure (.conditional condition whenTrue whenFalse)
      | _ => throw "callable: if statement requires a condition and one or two branches"
  | "WhileStmt" =>
      let children ← rawChildren statement
      let [condition, body] := children
        | throw "callable: while statement requires a condition and body"
      let condition ← parseCallableExpression profile parameters expressionRows condition none none
      let body ← parseCallableStatement profile parameters expressionRows resultType body
      pure (.whileLoop condition body)
  | "NullStmt" => .ok .skip
  | "ExprWithCleanups" =>
      let children ← rawChildren statement
      let [child] := children
        | throw "callable: expression cleanup wrapper requires one child"
      parseCallableStatement profile parameters expressionRows resultType child
  | "UnaryOperator" | "BinaryOperator" | "IntegerLiteral" | "DeclRefExpr" |
      "ImplicitCastExpr" | "ParenExpr" =>
      let expression ← parseCallableExpression profile parameters expressionRows statement none none
      pure (.expression expression)
  | _ => throw s!"callable: unsupported statement {kind}"

private def callableBody (profile : TargetProfile) (parameters : List CallableParameter)
    (expressionRows : List CppBinaryExpressionEvidence) (resultType : CppTypeEvidence)
    (body : Raw) : Except String CallableStatement := do
  unless body.text "kind" == some "CompoundStmt" do
    throw "callable: body is not a compound statement"
  parseCallableStatement profile parameters expressionRows resultType body

def admitCallableFunction (probe : DeclarationProbe)
    (typeRows : List TypeEvidenceRow) (expressionRows : List CppBinaryExpressionEvidence)
    (profile : TargetProfile) (path : List Nat) : Except String CallableFunction := do
  unless profile.valid do throw "callable: invalid target profile"
  let admitted ← admitLocalFunctionDeclaration probe path
  let body ← match admitted.form with
    | .compound body => pure body
    | .declaration => throw "callable: prototype has no callable body"
    | .deleted => throw "callable: deleted function has no callable body"
    | .functionTry _ => throw "callable: function-try body is outside the body profile"
  let functionRow ← callableTypeRow typeRows {value := admitted.occurrence.id}
  let declarationRow ← localFunctionRow probe admitted.occurrence.id
  unless functionRow.canonical == declarationRow.canonical do
    throw "callable: function type canonical handle disagrees with declaration"
  let signature ← callableSignature functionRow.type
  let parameters ← callableParameters admitted.parameters typeRows signature.parameters
  let typedBody ← callableBody profile parameters expressionRows signature.result body
  pure {occurrence := admitted.occurrence, signature, parameters, body := typedBody}

def admitCallableFunctionFromProbe (probe : DeclarationProbe) (profile : TargetProfile)
    (path : List Nat) : Except String CallableFunction := do
  let typeRows ← parseValidatedTypeEvidence probe
  let expressionRows ← parseValidatedBinaryExpressionEvidence probe
  admitCallableFunction probe typeRows expressionRows profile path

end LeanModels.Cpp
