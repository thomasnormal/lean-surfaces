import LeanModels.Cpp.LocalFunction
import LeanModels.Cpp.ExpressionEvidence
import LeanModels.Cpp.AutomaticDeclarations

namespace LeanModels.Cpp

open AdmittedAutomaticDeclStmt

mutual
  inductive CallableExpression where
    | integer (value : Nat)
    | parameter (declaration : FrontendHandle)
    | increment (operator : String) (isPostfix : Bool) (declaration : FrontendHandle)
    | convert (operand : TypedCallableExpression)
    | unary (operator : String) (operand : TypedCallableExpression)
    | conditional (condition whenTrue whenFalse : TypedCallableExpression)
    | comma (left right : TypedCallableExpression)
    | logical (operator : String) (left right : TypedCallableExpression)
    | binary (operator : String) (left right : TypedCallableExpression)
    deriving Repr, BEq, Inhabited

  structure TypedCallableExpression where
    expression : CallableExpression
    sourceType : CppTypeEvidence
    type : CppTypeEvidence
    deriving Repr, BEq, Inhabited

  inductive CallableStatement where
    | skip
    /-- A frontend-admitted automatic declaration sequence. -/
    | automatic (declaration : AdmittedAutomaticDeclStmt)
    /-- A retained source compound-statement boundary; declarations remain out of tier. -/
    | block (body : CallableStatement)
    | expression (expression : TypedCallableExpression)
    | assign (declaration : FrontendHandle) (expression : TypedCallableExpression)
    | compoundAssign (operator : String) (declaration : FrontendHandle)
        (expression : TypedCallableExpression)
    | returnVoid
    | return_ (expression : TypedCallableExpression)
    | conditional (condition : TypedCallableExpression)
        (whenTrue whenFalse : CallableStatement)
    | switch_ (condition : TypedCallableExpression) (clauses : List CallableSwitchClause)
    | whileLoop (condition : TypedCallableExpression) (body : CallableStatement)
    | doWhile (body : CallableStatement) (condition : TypedCallableExpression)
    | forLoop (initializer : CallableStatement) (condition : TypedCallableExpression)
        (step body : CallableStatement)
    | break_
    | continue_
    | sequence (first second : CallableStatement)
    deriving Repr, BEq, Inhabited

structure CallableSwitchClause where
  label : Option Int
  body : CallableStatement
  deriving Repr, BEq, Inhabited
end

mutual
  def CallableExpression.hasEffects : CallableExpression → Bool
    | .increment _ _ _ => true
    | .convert operand | .unary _ operand => operand.hasEffects
    | .conditional condition whenTrue whenFalse =>
        condition.hasEffects || whenTrue.hasEffects || whenFalse.hasEffects
    | .comma left right | .logical _ left right | .binary _ left right =>
        left.hasEffects || right.hasEffects
    | _ => false

  def TypedCallableExpression.hasEffects : TypedCallableExpression → Bool
    | ⟨expression, _, _⟩ => expression.hasEffects
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

private def switchLabelKind (raw : Raw) : Except String Bool := do
  let kind ← evidenceText raw "kind"
  pure (kind == "CaseStmt" || kind == "DefaultStmt")

private def switchCaseValue (raw : Raw) : Except String Int := do
  let kind ← evidenceText raw "kind"
  unless kind == "ConstantExpr" || kind == "IntegerLiteral" do
    throw "callable: switch case requires an integral constant expression"
  let type ← evidenceField raw "type"
  unless type.text "qualType" == some "int" do
    throw "callable: switch case requires an exact int label"
  let value ← evidenceText raw "value"
  match value.toInt? with
  | some value => pure value
  | none => throw "callable: switch case label is not an integer"

private def switchClauseRaws (raws : List Raw) : Except String (List Raw × List Raw) :=
  match raws with
  | [] => .ok ([], [])
  | raw :: rest => do
      if ← switchLabelKind raw then
        pure ([], raw :: rest)
      else
        let (body, remaining) ← switchClauseRaws rest
        pure (raw :: body, remaining)

private partial def switchClauses (raws : List Raw) : Except String (List (Option Int × List Raw)) := do
  match raws with
  | [] => pure []
  | raw :: rest =>
      let kind ← evidenceText raw "kind"
      let inner ← rawChildren raw
      let (label, initialBody) ← match kind with
        | "CaseStmt" =>
            let labelRaw :: body := inner
              | throw "callable: case statement requires a label"
            pure (some (← switchCaseValue labelRaw), body)
        | "DefaultStmt" => pure (none, inner)
        | _ => throw "callable: switch body must contain only case/default labels"
      let (tailBody, remaining) ← switchClauseRaws rest
      let clauses ← switchClauses remaining
      pure ((label, initialBody ++ tailBody) :: clauses)

private def switchLabelsValid : List (Option Int × List Raw) → Bool
  | [] => true
  | (label, _) :: rest =>
      (match label with
      | none => !rest.any (fun clause => clause.1.isNone)
      | some value => !rest.any (fun clause => clause.1 == some value)) && switchLabelsValid rest

private def callableBuiltin : CppTypeEvidence → Bool
  | .builtin _ => true
  | .qualified _ _ base => callableBuiltin base
  | _ => false

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
          | .lvalueReference referent => integralParameter referent
          | type => integralParameter type) then
        .error "callable: non-integral parameter type is outside the body profile"
      else match result with
        | .void | .builtin _ => .ok {result, parameters, variadic}
        | _ => .error "callable: non-integral result type is outside the body profile"
  | _ => .error "callable: declaration type is not a function type"
where
  integralParameter : CppTypeEvidence → Bool
    | .builtin _ => true
    | .qualified _ false base => integralParameter base
    | _ => false

private def callableParameters (rawParameters : List Raw) (rows : List TypeEvidenceRow)
    (expected : List CppTypeEvidence) : Except String (List CallableParameter) := do
  if rawParameters.length != expected.length then
    throw "callable: parameter count disagrees with function type"
  let mut result : List CallableParameter := []
  for (raw, expectedType) in rawParameters.zip expected do
    unless raw.text "kind" == some "ParmVarDecl" do
      throw "callable: unsupported direct function child"
    let declaration ← rawId raw
    if result.any (fun parameter => parameter.declaration == declaration) then
      throw "callable: duplicate parameter declaration handle"
    let row ← callableTypeRow rows declaration
    unless row.type == expectedType do
      throw "callable: parameter type disagrees with function type"
    result := result ++ [{declaration, name := raw.text "name", type := row.type}]
  pure result

private def parameterType? (parameters : List CallableParameter) (declaration : FrontendHandle) :
    Option CppTypeEvidence :=
  parameters.find? (fun parameter => parameter.declaration == declaration) |>.map (·.type)

private def integralRValueType : CppTypeEvidence → Option CppTypeEvidence
  | .builtin type => some (.builtin type)
  | .qualified _ false base => integralRValueType base
  | _ => none

private def validateCommaIntegralTyping (row : CppBinaryExpressionEvidence) : Except String Unit := do
  let some left := row.operands[0]?
    | throw "callable: comma expression lacks a left operand"
  let some right := row.operands[1]?
    | throw "callable: comma expression lacks a right operand"
  unless callableBuiltin left.sourceType && callableBuiltin left.type &&
      callableBuiltin right.sourceType && callableBuiltin right.type do
    throw "callable: comma expression requires builtin integral operands"
  unless row.result == right.type do
    throw "callable: comma expression result must be its right operand type"

private def referencedDeclaration (raw : Raw) : Except String FrontendHandle := do
  let reference ← evidenceField raw "referencedDecl"
  rawId reference

def compoundAssignmentOperator? (operator : String) : Option String :=
  match operator with
  | "+=" => some "+"
  | "-=" => some "-"
  | "*=" => some "*"
  | "/=" => some "/"
  | "%=" => some "%"
  | "&=" => some "&"
  | "|=" => some "|"
  | "^=" => some "^"
  | "<<=" => some "<<"
  | ">>=" => some ">>"
  | _ => none

private def integerLiteral (raw : Raw) (sourceExpected typeExpected : Option CppTypeEvidence)
    (witnessed : Option CppTypeEvidence) : Except String TypedCallableExpression := do
  let value ← evidenceText raw "value"
  let some value := value.toNat?
    | throw "callable: only nonnegative decimal integer literals are admitted"
  let type ← match witnessed with
    | some (.builtin integer) =>
        if integer == .boolean then throw "callable: integer literal has boolean type"
        else pure (.builtin integer)
    | some _ => throw "callable: integer literal requires a builtin integral type"
    | none => do
        let type ← evidenceField raw "type"
        unless type.text "qualType" == some "int" do
          throw "callable: legacy integer literal requires an exact int source type"
        pure (.builtin .int)
  unless sourceExpected.all (· == type) && typeExpected.all (· == type) do
    throw "callable: integer literal type disagrees with expression evidence"
  pure {expression := .integer value, sourceType := type, type}

partial def parseCallableExpressionTyped (profile : TargetProfile)
    (parameters : List CallableParameter)
    (expressionRows : List CppBinaryExpressionEvidence)
    (expressionTypes : Option (List CppExpressionTypeEvidence))
    (raw : Raw) (sourceExpected typeExpected : Option CppTypeEvidence) :
    Except String TypedCallableExpression := do
  let kind ← evidenceText raw "kind"
  let witnessed ← expressionTypes.mapM (fun rows => expressionTypeFor rows raw)
  if let some type := witnessed then
    unless typeExpected.all (· == type) do
      throw "callable: expression type disagrees with expected type"
  let typeExpected := witnessed.orElse (fun _ => typeExpected)
  match kind with
  | "IntegerLiteral" => integerLiteral raw sourceExpected typeExpected witnessed
  | "CXXBoolLiteralExpr" =>
      unless sourceExpected.all (· == .builtin .boolean) &&
          typeExpected.all (· == .builtin .boolean) do
        throw "callable: boolean literal type disagrees with evidence"
      let value ← evidenceBool raw "value"
      pure {
        expression := .integer (if value then 1 else 0)
        sourceType := .builtin .boolean
        type := .builtin .boolean
      }
  | "DeclRefExpr" =>
      let reference ← evidenceField raw "referencedDecl"
      let declaration ← rawId reference
      let some parameterType := parameterType? parameters declaration
        | throw "callable: expression references a non-parameter declaration"
      unless witnessed.all (· == parameterType) do
        throw "callable: reference type disagrees with bound declaration"
      if sourceExpected.isSome && sourceExpected != some parameterType then
        throw "callable: parameter source type disagrees with expression evidence"
      if sourceExpected.isNone && typeExpected.isSome && typeExpected != some parameterType then
        throw "callable: parameter return conversion is outside the body profile"
      let type := typeExpected.getD parameterType
      pure {expression := .parameter declaration, sourceType := parameterType, type}
  | "ImplicitCastExpr" =>
      let castKind ← evidenceText raw "castKind"
      unless castKind == "LValueToRValue" || castKind == "NoOp" ||
          castKind == "IntegralToBoolean" || castKind == "IntegralCast" do
        throw s!"callable: unsupported implicit cast {castKind}"
      let children ← rawChildren raw
      match children with
      | [child] =>
          if castKind == "LValueToRValue" then
            let operand ← parseCallableExpressionTyped profile parameters expressionRows expressionTypes child sourceExpected none
            let some destination := integralRValueType operand.type
              | throw "callable: lvalue conversion requires a nonvolatile integral type"
            if typeExpected.isSome && typeExpected != some destination then
              throw "callable: lvalue conversion result disagrees with expected type"
            if operand.type == destination then pure operand
            else pure {expression := .convert operand, sourceType := operand.sourceType, type := destination}
          else if castKind == "IntegralToBoolean" || castKind == "IntegralCast" then
            let operand ← parseCallableExpressionTyped profile parameters expressionRows expressionTypes child none none
            let destination ← if castKind == "IntegralToBoolean" then
              pure (.builtin .boolean)
            else match typeExpected with
              | some type => pure type
              | none => throw "callable: integral cast lacks destination type evidence"
            unless callableBuiltin operand.type && callableBuiltin destination do
              throw "callable: integral cast requires builtin integral types"
            if typeExpected.isSome && typeExpected != some destination then
              throw "callable: integral cast result disagrees with expected type"
            pure {
              expression := .convert operand
              sourceType := operand.sourceType
              type := destination
            }
          else
            let operand ← parseCallableExpressionTyped profile parameters expressionRows expressionTypes child sourceExpected none
            let destination := typeExpected.getD operand.type
            unless (integralRValueType operand.type).isSome &&
                integralRValueType operand.type == integralRValueType destination do
              throw "callable: NoOp cast changes integral type or volatility"
            if operand.type == destination then pure operand
            else pure {expression := .convert operand, sourceType := operand.sourceType, type := destination}
      | _ => throw "callable: implicit cast must have one child"
  | "ParenExpr" =>
      let children ← rawChildren raw
      match children with
      | [child] => parseCallableExpressionTyped profile parameters expressionRows expressionTypes child sourceExpected typeExpected
      | _ => throw "callable: parenthesized expression must have one child"
  | "ConditionalOperator" =>
      let children ← rawChildren raw
      let [conditionRaw, whenTrueRaw, whenFalseRaw] := children
        | throw "callable: conditional expression requires three operands"
      let condition ← parseCallableExpressionTyped profile parameters expressionRows expressionTypes conditionRaw none none
      unless callableBuiltin condition.type do
        throw "callable: conditional condition must be a builtin integral expression"
      let whenTrue ← parseCallableExpressionTyped profile parameters expressionRows expressionTypes whenTrueRaw none typeExpected
      let whenFalse ← parseCallableExpressionTyped profile parameters expressionRows expressionTypes whenFalseRaw none typeExpected
      unless whenTrue.type == whenFalse.type do
        throw "callable: conditional branches require one represented type"
      pure {
        expression := .conditional condition whenTrue whenFalse
        sourceType := sourceExpected.getD whenTrue.type
        type := whenTrue.type
      }
  | "BinaryOperator" =>
      let occurrence ← rawId raw
      let some row := expressionRows.find? (fun row => row.occurrence == occurrence)
        | throw "callable: binary body expression lacks typed evidence"
      let logical := row.operator == "&&" || row.operator == "||"
      let comma := row.operator == ","
      if comma then
        validateCommaIntegralTyping row
      else if logical then
        unless row.result == .builtin .boolean do
          throw "callable: logical expression result is not boolean"
        unless row.operands.all (fun operand =>
            callableBuiltin operand.sourceType && callableBuiltin operand.type) do
          throw "callable: logical expression operands are not builtin integrals"
      else
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
          let left ← parseCallableExpressionTyped profile parameters expressionRows expressionTypes leftRaw
            (if logical then none else some leftEvidence.sourceType)
            (if logical then none else some leftEvidence.type)
          let right ← parseCallableExpressionTyped profile parameters expressionRows expressionTypes rightRaw
            (if logical then none else some rightEvidence.sourceType)
            (if logical then none else some rightEvidence.type)
          unless logical || comma || (!left.expression.hasEffects && !right.expression.hasEffects) do
            throw "callable: side effects in unsequenced binary operands are outside the body profile"
          pure {
            expression := if comma then .comma left right
              else if logical then .logical row.operator left right
              else .binary row.operator left right
            sourceType := sourceExpected.getD row.result
            type := row.result
          }
      | _, _ => throw "callable: binary body expression requires two operands"
  | "UnaryOperator" =>
      let operator ← evidenceText raw "opcode"
      if operator == "++" || operator == "--" then
        let isPostfix ← evidenceBool raw "isPostfix"
        let children ← rawChildren raw
        let [target] := children
          | throw "callable: increment requires exactly one target"
        unless target.text "kind" == some "DeclRefExpr" do
          throw "callable: increment target must be a parameter reference"
        let declaration ← referencedDeclaration target
        let some targetType := parameterType? parameters declaration
          | throw "callable: increment target is not a parameter"
        unless targetType != .builtin .boolean && callableBuiltin targetType do
          throw "callable: increment requires a non-boolean integral parameter"
        if typeExpected.isSome && typeExpected != some targetType then
          throw "callable: increment result type disagrees with expected type"
        return ({
          expression := .increment operator isPostfix declaration
          sourceType := targetType
          type := targetType
        } : TypedCallableExpression)
      unless operator == "+" || operator == "-" || operator == "~" || operator == "!" do
        throw s!"callable: unsupported unary operator {operator}"
      let children ← rawChildren raw
      let [child] := children
        | throw "callable: unary body expression requires one operand"
      let operand ← parseCallableExpressionTyped profile parameters expressionRows expressionTypes child none none
      let some operandType := integralRValueType operand.type
        | throw "callable: unary operand is not a nonvolatile integral value"
      let .builtin integer := operandType
        | throw "callable: unary operand requires a builtin integral type"
      if operator == "!" then
        unless witnessed.isNone || integer == .boolean do
          throw "callable: logical negation lacks contextual boolean conversion"
      else
        let promoted ← match integralPromotion profile integer with
          | .ok type => pure type
          | .error _ => throw "callable: unary promotion is unresolved"
        unless operand.type == .builtin promoted do
          throw "callable: unary operand lacks integral promotion"
      let type := if operator == "!" then .builtin .boolean else operand.type
      if typeExpected.isSome && typeExpected != some type then
        throw "callable: unary result type disagrees with expected type"
      pure {expression := .unary operator operand, sourceType := type, type}
  | _ => throw s!"callable: unsupported return expression {kind}"

/-- Legacy expression entry point. Unknown cast destinations remain loud. -/
def parseCallableExpression (profile : TargetProfile) (parameters : List CallableParameter)
    (expressionRows : List CppBinaryExpressionEvidence) (raw : Raw)
    (sourceExpected typeExpected : Option CppTypeEvidence) : Except String TypedCallableExpression :=
  parseCallableExpressionTyped profile parameters expressionRows none raw sourceExpected typeExpected

mutual
  private partial def parseCallableSequence (profile : TargetProfile)
      (parameters : List CallableParameter)
      (expressionRows : List CppBinaryExpressionEvidence)
      (resultType : CppTypeEvidence) : List Raw → Except String CallableStatement
    | [] => .ok .skip
    | first :: rest => do
        let first ← parseCallableStatement profile parameters expressionRows resultType first
        rest.foldlM (init := first) fun accumulated child => do
          let parsed ← parseCallableStatement profile parameters expressionRows resultType child
          pure (.sequence accumulated parsed)

  partial def parseCallableStatement (profile : TargetProfile)
      (parameters : List CallableParameter)
      (expressionRows : List CppBinaryExpressionEvidence)
      (resultType : CppTypeEvidence) (statement : Raw) : Except String CallableStatement := do
  let kind ← evidenceText statement "kind"
  match kind with
  | "CompoundStmt" =>
      let children ← rawChildren statement
      let body ← parseCallableSequence profile parameters expressionRows resultType children
      pure (.block body)
  | "ReturnStmt" =>
      let values ← rawChildren statement
      if resultType == .void then
        unless values.isEmpty do
          throw "callable: void-valued return expressions are outside the body profile"
        return .returnVoid
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
  | "SwitchStmt" =>
      let children ← rawChildren statement
      let [conditionRaw, bodyRaw] := children
        | throw "callable: switch statement requires a condition and body"
      let condition ← parseCallableExpression profile parameters expressionRows conditionRaw none none
      unless condition.type == .builtin .int do
        throw "callable: switch condition requires an exact int expression"
      unless bodyRaw.text "kind" == some "CompoundStmt" do
        throw "callable: switch body must be a compound statement"
      let bodyRaws ← rawChildren bodyRaw
      let clauseRaws ← switchClauses bodyRaws
      unless switchLabelsValid clauseRaws do
        throw "callable: switch labels must be unique with at most one default"
      let clauses ← clauseRaws.mapM fun (label, raws) => do
        let body ← parseCallableSequence profile parameters expressionRows resultType raws
        pure {label, body}
      pure (.switch_ condition clauses)
  | "WhileStmt" =>
      let children ← rawChildren statement
      let [condition, body] := children
        | throw "callable: while statement requires a condition and body"
      let condition ← parseCallableExpression profile parameters expressionRows condition none none
      let body ← parseCallableStatement profile parameters expressionRows resultType body
      pure (.whileLoop condition body)
  | "ForStmt" =>
      let children ← rawChildren statement
      let [initializer, conditionVariable, condition, step, body] := children
        | throw "callable: for statement requires initializer, condition, step and body"
      unless conditionVariable == .object [] do
        throw "callable: for loop condition declarations are outside the body profile"
      let initializer ← parseCallableStatement profile parameters expressionRows resultType initializer
      let condition ← parseCallableExpression profile parameters expressionRows condition none none
      let body ← parseCallableStatement profile parameters expressionRows resultType body
      let step ← parseCallableStatement profile parameters expressionRows resultType step
      pure (.forLoop initializer condition step body)
  | "DoStmt" =>
      let children ← rawChildren statement
      let [body, condition] := children
        | throw "callable: do statement requires a body and condition"
      let body ← parseCallableStatement profile parameters expressionRows resultType body
      let condition ← parseCallableExpression profile parameters expressionRows condition none none
      pure (.doWhile body condition)
  | "BreakStmt" => .ok .break_
  | "ContinueStmt" => .ok .continue_
  | "NullStmt" => .ok .skip
  | "ExprWithCleanups" =>
      let children ← rawChildren statement
      let [child] := children
        | throw "callable: expression cleanup wrapper requires one child"
      parseCallableStatement profile parameters expressionRows resultType child
  | "BinaryOperator" =>
      let operator ← evidenceText statement "opcode"
      if operator == "=" then
        let children ← rawChildren statement
        let [target, value] := children
          | throw "callable: assignment requires a target and value"
        unless target.text "kind" == some "DeclRefExpr" do
          throw "callable: assignment target must be a parameter reference"
        let declaration ← referencedDeclaration target
        let some targetType := parameterType? parameters declaration
          | throw "callable: assignment target is not a parameter"
        let expression ← parseCallableExpression profile parameters expressionRows value none
          (some targetType)
        pure (.assign declaration expression)
      else
        let expression ← parseCallableExpression profile parameters expressionRows statement none none
        pure (.expression expression)
  | "CompoundAssignOperator" =>
      let operator ← evidenceText statement "opcode"
      let some arithmeticOperator := compoundAssignmentOperator? operator
        | throw s!"callable: unsupported compound assignment {operator}"
      let occurrence ← rawId statement
      let some row := expressionRows.find? (fun row => row.occurrence == occurrence)
        | throw "callable: compound assignment lacks typed evidence"
      unless row.operator == operator do
        throw "callable: compound assignment operator disagrees with typed evidence"
      let typedRow := {row with operator := arithmeticOperator}
      validateBinaryIntegralTyping profile typedRow
      let children ← rawChildren statement
      let [target, value] := children
        | throw "callable: compound assignment requires a target and value"
      unless target.text "kind" == some "DeclRefExpr" do
        throw "callable: compound assignment target must be a parameter reference"
      let declaration ← referencedDeclaration target
      let some targetType := parameterType? parameters declaration
        | throw "callable: compound assignment target is not a parameter"
      unless row.result == targetType do
        throw "callable: compound assignment result disagrees with target type"
      let some leftEvidence := row.operands[0]?
        | throw "callable: compound assignment lacks a left operand"
      unless target.text "id" == some leftEvidence.occurrence.value &&
          target.text "kind" == some leftEvidence.kind &&
          leftEvidence.sourceType == targetType && leftEvidence.type == targetType do
        throw "callable: compound assignment target disagrees with typed evidence"
      let some rightEvidence := row.operands[1]?
        | throw "callable: compound assignment lacks a right operand"
      unless value.text "id" == some rightEvidence.occurrence.value &&
          value.text "kind" == some rightEvidence.kind do
        throw "callable: compound assignment operand disagrees with typed evidence"
      let expression ← parseCallableExpression profile parameters expressionRows value
        (some rightEvidence.sourceType) (some rightEvidence.type)
      pure (.compoundAssign operator declaration expression)
  | "UnaryOperator" | "IntegerLiteral" | "CXXBoolLiteralExpr" | "DeclRefExpr" |
      "ImplicitCastExpr" | "ParenExpr" =>
      let expression ← parseCallableExpression profile parameters expressionRows statement none none
      pure (.expression expression)
    | _ => throw s!"callable: unsupported statement {kind}"
end

private def callableBody (profile : TargetProfile) (parameters : List CallableParameter)
    (expressionRows : List CppBinaryExpressionEvidence) (resultType : CppTypeEvidence)
    (body : Raw) : Except String CallableStatement := do
  unless body.text "kind" == some "CompoundStmt" do
    throw "callable: body is not a compound statement"
  parseCallableStatement profile parameters expressionRows resultType body

private partial def rawHasKind (raw : Raw) (wanted : String) : Bool :=
  (raw.text "kind" == some wanted) ||
    match raw with
    | .array values => values.any (fun value => rawHasKind value wanted)
    | .object fields => fields.any (fun (_, value) => rawHasKind value wanted)
    | _ => false

/-! The object-backed parser below is deliberately separate from the original
value-only parser. Existing callers therefore retain the old loud refusal for
DeclStmt, while complete callable admission can opt into the same source tree
with declaration evidence and a lexical handle environment. -/

private def localParameter (declaration : FrontendHandle) (type : CppTypeEvidence) :
    CallableParameter := {declaration, name := none, type}

private def localParameters (rows : List TypeEvidenceRow)
    (available : List CallableParameter) (declarations : List FrontendHandle) :
    Except String (List CallableParameter) := do
  let mut result : List CallableParameter := []
  for declaration in declarations do
    if (available ++ result).any (fun parameter => parameter.declaration == declaration) then
      throw "callable: duplicate local declaration handle"
    let found := rows.filter (fun row => row.occurrence == declaration)
    let some row := found.head?
      | throw "callable: local declaration lacks structured type evidence"
    unless found.all (· == row) do
      throw "callable: conflicting local declaration type evidence"
    let type := match row.type with
      | .lvalueReference referent => referent
      | type => type
    result := result ++ [localParameter declaration type]
  pure result

private def admitAutomaticAt (probe : DeclarationProbe)
    (typeRows : List TypeEvidenceRow) (variableRows : List CppVariableEvidence)
    (expressionRows : List CppBinaryExpressionEvidence) (profile : TargetProfile)
    (available : List CallableParameter) (statement : Raw) :
    Except String AdmittedAutomaticDeclStmt := do
  let localProbe : DeclarationProbe := {probe with ast := statement}
  admit localProbe typeRows variableRows expressionRows profile
    (available.map (·.declaration)) []

mutual
partial def callableSequenceWithLocals (probe : DeclarationProbe)
    (typeRows : List TypeEvidenceRow) (variableRows : List CppVariableEvidence)
    (expressionRows : List CppBinaryExpressionEvidence)
    (expressionTypes : Option (List CppExpressionTypeEvidence)) (profile : TargetProfile)
    (resultType : CppTypeEvidence) (scope : List CallableParameter)
    (statements : List Raw) :
    Except String (CallableStatement × List CallableParameter) := do
  match statements with
  | [] => pure (.skip, scope)
  | raw :: rest => do
      let parsed ← parseCallableStatementWithLocals probe typeRows variableRows
        expressionRows expressionTypes profile resultType scope raw
      let (first, updated) := parsed
      match rest with
      | [] => pure (first, updated)
      | _ =>
          let (tail, finalScope) ← callableSequenceWithLocals probe typeRows variableRows
            expressionRows expressionTypes profile resultType updated rest
          pure (.sequence first tail, finalScope)

partial def parseCallableCompoundWithLocals (probe : DeclarationProbe)
    (typeRows : List TypeEvidenceRow) (variableRows : List CppVariableEvidence)
    (expressionRows : List CppBinaryExpressionEvidence)
    (expressionTypes : Option (List CppExpressionTypeEvidence)) (profile : TargetProfile)
    (resultType : CppTypeEvidence) (scope : List CallableParameter) (raw : Raw)
    (exportLocals : Bool) :
    Except String (CallableStatement × List CallableParameter) := do
  let children ← rawChildren raw
  let (body, updated) ← callableSequenceWithLocals probe typeRows variableRows
    expressionRows expressionTypes profile resultType scope children
  pure (.block body, if exportLocals then updated else scope)

partial def parseCallableSubstatementWithLocals (probe : DeclarationProbe)
    (typeRows : List TypeEvidenceRow) (variableRows : List CppVariableEvidence)
    (expressionRows : List CppBinaryExpressionEvidence)
    (expressionTypes : Option (List CppExpressionTypeEvidence)) (profile : TargetProfile)
    (resultType : CppTypeEvidence) (scope : List CallableParameter) (raw : Raw) :
    Except String (CallableStatement × List CallableParameter) := do
  let parsed ← parseCallableStatementWithLocals probe typeRows variableRows expressionRows expressionTypes
    profile resultType scope raw
  if raw.text "kind" == some "CompoundStmt" then
    pure parsed
  else
    pure (.block parsed.1, scope)

partial def parseCallableStatementWithLocals (probe : DeclarationProbe)
    (typeRows : List TypeEvidenceRow) (variableRows : List CppVariableEvidence)
    (expressionRows : List CppBinaryExpressionEvidence)
    (expressionTypes : Option (List CppExpressionTypeEvidence)) (profile : TargetProfile)
    (resultType : CppTypeEvidence) (scope : List CallableParameter) (statement : Raw) :
    Except String (CallableStatement × List CallableParameter) := do
  let allParameters := scope
  let kind ← evidenceText statement "kind"
  match kind with
  | "DeclStmt" =>
      let admitted ← admitAutomaticAt probe typeRows variableRows expressionRows profile
        allParameters statement
      let locals ← localParameters typeRows allParameters admitted.declarations
      pure (.automatic admitted, allParameters ++ locals)
  | "CompoundStmt" =>
      parseCallableCompoundWithLocals probe typeRows variableRows expressionRows expressionTypes profile
        resultType scope statement false
  | "ReturnStmt" =>
      let values ← rawChildren statement
      if resultType == .void then
        unless values.isEmpty do
          throw "callable: void-valued return expressions are outside the body profile"
        return (.returnVoid, scope)
      let [value] := values
        | throw "callable: return statement requires exactly one expression"
      let expression ← parseCallableExpressionTyped profile allParameters expressionRows expressionTypes value none
        (some resultType)
      unless expression.type == resultType do
        throw "callable: return expression type disagrees with function result"
      pure (.return_ expression, scope)
  | "IfStmt" =>
      let children ← rawChildren statement
      match children with
      | [condition, whenTrue] | [condition, whenTrue, _] =>
          let condition ← parseCallableExpressionTyped profile allParameters expressionRows expressionTypes condition none none
          let (whenTrue, _) ← parseCallableSubstatementWithLocals probe typeRows variableRows
            expressionRows expressionTypes profile resultType scope whenTrue
          let whenFalse ← match children with
            | [_, _, otherwise] =>
                (parseCallableSubstatementWithLocals probe typeRows variableRows expressionRows
                  expressionTypes profile resultType scope otherwise).map Prod.fst
            | _ => .ok .skip
          pure (.conditional condition whenTrue whenFalse, scope)
      | _ => throw "callable: if statement requires a condition and one or two branches"
  | "SwitchStmt" =>
      let children ← rawChildren statement
      let [conditionRaw, bodyRaw] := children
        | throw "callable: switch statement requires a condition and body"
      let condition ← parseCallableExpressionTyped profile allParameters expressionRows expressionTypes conditionRaw none none
      unless condition.type == .builtin .int do
        throw "callable: switch condition requires an exact int expression"
      unless bodyRaw.text "kind" == some "CompoundStmt" do
        throw "callable: switch body must be a compound statement"
      let bodyRaws ← rawChildren bodyRaw
      let clauseRaws ← switchClauses bodyRaws
      unless switchLabelsValid clauseRaws do
        throw "callable: switch labels must be unique with at most one default"
      let clauses ← clauseRaws.mapM fun (label, raws) => do
        let (body, _) ← callableSequenceWithLocals probe typeRows variableRows expressionRows
          expressionTypes profile resultType scope raws
        pure {label, body}
      pure (.switch_ condition clauses, scope)
  | "WhileStmt" =>
      let children ← rawChildren statement
      let [condition, body] := children
        | throw "callable: while statement requires a condition and body"
      let condition ← parseCallableExpressionTyped profile allParameters expressionRows expressionTypes condition none none
      let (body, _) ← parseCallableSubstatementWithLocals probe typeRows variableRows
        expressionRows expressionTypes profile resultType scope body
      pure (.whileLoop condition body, scope)
  | "ForStmt" =>
      let children ← rawChildren statement
      let [initializer, conditionVariable, condition, step, body] := children
        | throw "callable: for statement requires initializer, condition, step and body"
      unless conditionVariable == .object [] do
        throw "callable: for loop condition declarations are outside the body profile"
      let (initializer, loopScope) ← parseCallableStatementWithLocals probe typeRows variableRows
        expressionRows expressionTypes profile resultType scope initializer
      let condition ← parseCallableExpressionTyped profile loopScope expressionRows expressionTypes condition none none
      let (body, _) ← parseCallableSubstatementWithLocals probe typeRows variableRows
        expressionRows expressionTypes profile resultType loopScope body
      let (step, _) ← parseCallableStatementWithLocals probe typeRows variableRows
        expressionRows expressionTypes profile resultType loopScope step
      pure (.forLoop initializer condition step body, scope)
  | "DoStmt" =>
      let children ← rawChildren statement
      let [body, condition] := children
        | throw "callable: do statement requires a body and condition"
      let (body, _) ← parseCallableSubstatementWithLocals probe typeRows variableRows
        expressionRows expressionTypes profile resultType scope body
      let condition ← parseCallableExpressionTyped profile allParameters expressionRows expressionTypes condition none none
      pure (.doWhile body condition, scope)
  | "BreakStmt" => pure (.break_, scope)
  | "ContinueStmt" => pure (.continue_, scope)
  | "NullStmt" => pure (.skip, scope)
  | "ExprWithCleanups" =>
      let children ← rawChildren statement
      let [child] := children
        | throw "callable: expression cleanup wrapper requires one child"
      parseCallableStatementWithLocals probe typeRows variableRows expressionRows expressionTypes profile
        resultType scope child
  | "BinaryOperator" =>
      let operator ← evidenceText statement "opcode"
      if operator == "=" then
        let children ← rawChildren statement
        let [target, value] := children
          | throw "callable: assignment requires a target and value"
        unless target.text "kind" == some "DeclRefExpr" do
          throw "callable: assignment target must be a bound declaration reference"
        let declaration ← referencedDeclaration target
        let some targetParameter := allParameters.find? (fun p => p.declaration == declaration)
          | throw "callable: assignment target is not a bound declaration"
        let expression ← parseCallableExpressionTyped profile allParameters expressionRows expressionTypes value none
          (some targetParameter.type)
        pure (.assign declaration expression, scope)
      else
        let expression ← parseCallableExpressionTyped profile allParameters expressionRows expressionTypes statement none none
        pure (.expression expression, scope)
  | "CompoundAssignOperator" =>
      let operator ← evidenceText statement "opcode"
      let some arithmeticOperator := compoundAssignmentOperator? operator
        | throw s!"callable: unsupported compound assignment {operator}"
      let occurrence ← rawId statement
      let some row := expressionRows.find? (fun row => row.occurrence == occurrence)
        | throw "callable: compound assignment lacks typed evidence"
      unless row.operator == operator do
        throw "callable: compound assignment operator disagrees with typed evidence"
      let typedRow := {row with operator := arithmeticOperator}
      validateBinaryIntegralTyping profile typedRow
      let children ← rawChildren statement
      let [target, value] := children
        | throw "callable: compound assignment requires a target and value"
      unless target.text "kind" == some "DeclRefExpr" do
        throw "callable: compound assignment target must be a bound declaration reference"
      let declaration ← referencedDeclaration target
      let some targetParameter := allParameters.find? (fun p => p.declaration == declaration)
        | throw "callable: compound assignment target is not a bound declaration"
      let some leftEvidence := row.operands[0]?
        | throw "callable: compound assignment lacks a left operand"
      unless target.text "id" == some leftEvidence.occurrence.value &&
          target.text "kind" == some leftEvidence.kind &&
          leftEvidence.sourceType == targetParameter.type && leftEvidence.type == targetParameter.type do
        throw "callable: compound assignment target disagrees with typed evidence"
      let some rightEvidence := row.operands[1]?
        | throw "callable: compound assignment lacks a right operand"
      let expression ← parseCallableExpressionTyped profile allParameters expressionRows expressionTypes value
        (some rightEvidence.sourceType) (some rightEvidence.type)
      pure (.compoundAssign operator declaration expression, scope)
  | "UnaryOperator" | "IntegerLiteral" | "CXXBoolLiteralExpr" | "DeclRefExpr" |
      "ImplicitCastExpr" | "ParenExpr" =>
      let expression ← parseCallableExpressionTyped profile allParameters expressionRows expressionTypes statement none none
      pure (.expression expression, scope)
  | _ => throw s!"callable: unsupported statement {kind}"
end

private def callableBodyWithLocals (probe : DeclarationProbe)
    (typeRows : List TypeEvidenceRow) (variableRows : List CppVariableEvidence)
    (expressionRows : List CppBinaryExpressionEvidence)
    (expressionTypes : Option (List CppExpressionTypeEvidence)) (profile : TargetProfile)
    (parameters : List CallableParameter) (resultType : CppTypeEvidence) (body : Raw) :
    Except String CallableStatement := do
  unless body.text "kind" == some "CompoundStmt" do
    throw "callable: body is not a compound statement"
  let (parsed, _) ← parseCallableCompoundWithLocals probe typeRows variableRows expressionRows expressionTypes
    profile resultType parameters body true
  pure parsed

/-- Consume already-validated declaration, binary and expression-type rows from
this probe. `admitCallableFunction` validates the latter for single calls. -/
def admitCallableFunctionWithExpressionTypes (probe : DeclarationProbe)
    (typeRows : List TypeEvidenceRow) (expressionRows : List CppBinaryExpressionEvidence)
    (expressionTypes : Option (List CppExpressionTypeEvidence))
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
  let variableRows ← if rawHasKind body "DeclStmt" then
      parseValidatedVariableEvidence probe
    else pure []
  let expressionTypes := expressionTypes.map (expressionTypeRowsFor body)
  -- A named reference expression has the referent's type; keep the declared
  -- reference type in `parameters` for argument binding at frame entry.
  let expressionParameters := parameters.map fun parameter =>
    {parameter with type := match parameter.type with
      | .lvalueReference referent => referent
      | type => type}
  let typedBody ← callableBodyWithLocals probe typeRows variableRows expressionRows expressionTypes profile
    expressionParameters signature.result body
  pure {occurrence := admitted.occurrence, signature, parameters, body := typedBody}

def admitCallableFunction (probe : DeclarationProbe)
    (typeRows : List TypeEvidenceRow) (expressionRows : List CppBinaryExpressionEvidence)
    (profile : TargetProfile) (path : List Nat) : Except String CallableFunction := do
  let expressionTypes ← parseValidatedExpressionTypeEvidence probe
  admitCallableFunctionWithExpressionTypes probe typeRows expressionRows expressionTypes profile path

def admitCallableFunctionFromProbe (probe : DeclarationProbe) (profile : TargetProfile)
    (path : List Nat) : Except String CallableFunction := do
  let typeRows ← parseValidatedTypeEvidence probe
  let expressionRows ← parseValidatedBinaryExpressionEvidence probe
  admitCallableFunction probe typeRows expressionRows profile path

end LeanModels.Cpp
