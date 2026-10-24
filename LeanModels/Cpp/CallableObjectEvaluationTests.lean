import LeanModels.Cpp.CallableObjectEvaluation
import LeanModels.Cpp.CallableEvaluation

namespace LeanModels.Cpp.CallableObjectEvaluationTests

open CallableObjectEvaluation
open IntegralObjectFrame

private def handle (value : String) : FrontendHandle := {value}
private def intType : CppTypeEvidence := .builtin .int
private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩
private def unsignedLongType : CppTypeEvidence := .builtin .unsignedLong
private def shortType : CppTypeEvidence := .builtin .short

private def functionDeclaration : Declaration := {
  id := "0x2", kind := "FunctionDecl", path := [0], name := some "local_read",
  lexicalParents := [], semanticParent := none, previousDecl := none,
  mangledName := none, type := none, location := none, range := none
}

private def parameter : CallableParameter :=
  {declaration := handle "0x10", name := some "value", type := intType}

private def functionWithLocal (initializer : Expression) : CallableFunction := {
  occurrence := functionDeclaration,
  signature := {result := intType, parameters := [intType], variadic := false},
  parameters := [parameter],
  body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType initializer
      declarations := [handle "0x11"]})
    (.return_ {
      expression := .parameter (handle "0x11"),
      sourceType := intType, type := intType}))
}

private def alignOfObject : Bool :=
  let function : CallableFunction := {
    occurrence := functionDeclaration
    signature := {result := unsignedLongType, parameters := [], variadic := false}
    parameters := []
    body := .block (.return_ {
      expression := .alignOf shortType
      sourceType := unsignedLongType
      type := unsignedLongType})}
  match evaluateCallableObject 16 .lp64 function [] with
  | .ok (.ok value) => value == ⟨.unsigned 64, 2⟩
  | _ => false

#guard alignOfObject

private def automaticLiteral (declaration : String) (value : Int) : CallableStatement :=
  .automatic {
    statement := .declare (handle declaration) intType intType (.literal (signed value))
    declarations := [handle declaration]}

private def localMutationFunction : CallableFunction :=
  {functionWithLocal (.literal (signed 4)) with
    body := .block (.sequence
      (automaticLiteral "0x11" 4)
      (.sequence
        (.assign (handle "0x11")
          {expression := CallableExpression.binary "+"
            {expression := CallableExpression.parameter (handle "0x11"),
              sourceType := intType, type := intType}
            {expression := CallableExpression.integer 3,
              sourceType := intType, type := intType},
            sourceType := intType, type := intType})
        (.return_ {
          expression := .parameter (handle "0x11"), sourceType := intType, type := intType}))) }

private def localMutation : Bool :=
  match evaluateCallableObject 32 .lp64 localMutationFunction [signed 7] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableLocalDeclarationWitness : Bool := localMutation

private def localIncrementFunction : CallableFunction :=
  {functionWithLocal (.literal (signed 4)) with
    body := .block (.sequence
      (automaticLiteral "0x11" 4)
      (.return_ {
        expression := CallableExpression.increment "++" false (handle "0x11"),
        sourceType := intType, type := intType})) }

private def localIncrement : Bool :=
  match evaluateCallableObject 32 .lp64 localIncrementFunction [signed 7] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalIncrementWitness : Bool := localIncrement

#guard callableLocalIncrementWitness

private def loopLocalReentryFunction : CallableFunction :=
  {functionWithLocal (.literal (signed 0)) with
    body := .block (.sequence
      (.whileLoop
        {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
        (.block (.sequence
          (automaticLiteral "0x12" 1)
          (.assign (handle "0x10")
            {expression := CallableExpression.binary "-"
              {expression := CallableExpression.parameter (handle "0x10"),
                sourceType := intType, type := intType}
              {expression := CallableExpression.integer 1,
                sourceType := intType, type := intType},
              sourceType := intType, type := intType}))))
      (.return_ {
        expression := .parameter (handle "0x10"), sourceType := intType, type := intType})) }

private def loopLocalReentry : Bool :=
  match CallableObjectFrame.start .lp64 loopLocalReentryFunction [signed 3] with
  | .ok callable =>
      let result := evaluateCallableObjectInFrame 128 callable
      match result.result with
      | .ok (.ok value) => value == signed 0 && result.frame.store.objects.objects.length == 4
      | _ => false
  | .error _ => false

private def forBodyFailureRetainsFrame : Bool :=
  let one : TypedCallableExpression := {
    expression := .integer 1, sourceType := intType, type := intType}
  let zero : TypedCallableExpression := {
    expression := .integer 0, sourceType := intType, type := intType}
  let failingExpression : TypedCallableExpression := {
    expression := .binary "/" one zero,
    sourceType := intType, type := intType}
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 0)) with
      body := .block (.forLoop .skip
        {expression := .integer 1, sourceType := intType, type := intType}
        .skip (.expression failingExpression))}
  match CallableObjectFrame.start .lp64 callable [signed 7] with
  | .ok started =>
      let result := evaluateCallableObjectInFrame 32 started
      result.frame.scopeDepth == 1 &&
        match result.result with
        | .ok (.undefined .divisionByZero) => true
        | _ => false
  | .error _ => false

def callableForBodyFailureRetainsFrameWitness : Bool := forBodyFailureRetainsFrame

private def returnFailureRetainsFrame : Bool :=
  let one : TypedCallableExpression := {
    expression := .integer 1, sourceType := intType, type := intType}
  let zero : TypedCallableExpression := {
    expression := .integer 0, sourceType := intType, type := intType}
  let failingExpression : TypedCallableExpression := {
    expression := .binary "/" one zero,
    sourceType := intType, type := intType}
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 0)) with
      body := .block (.return_ failingExpression)}
  match CallableObjectFrame.start .lp64 callable [signed 7] with
  | .ok started =>
      let result := evaluateCallableObjectInFrame 32 started
      result.frame.scopeDepth == 1 &&
        match result.result with
        | .ok (.undefined .divisionByZero) => true
        | _ => false
  | .error _ => false

def callableReturnFailureRetainsFrameWitness : Bool := returnFailureRetainsFrame

private def forInitializerFailureRetainsFrame : Bool :=
  let one : TypedCallableExpression := {
    expression := .integer 1, sourceType := intType, type := intType}
  let zero : TypedCallableExpression := {
    expression := .integer 0, sourceType := intType, type := intType}
  let failingExpression : TypedCallableExpression := {
    expression := .binary "/" one zero,
    sourceType := intType, type := intType}
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 0)) with
      body := .block (.forLoop (.expression failingExpression)
        {expression := .integer 1, sourceType := intType, type := intType}
        .skip .skip)}
  match CallableObjectFrame.start .lp64 callable [signed 7] with
  | .ok started =>
      let result := evaluateCallableObjectInFrame 32 started
      result.frame.scopeDepth == 1 &&
        match result.result with
        | .ok (.undefined .divisionByZero) => true
        | _ => false
  | .error _ => false

def callableForInitializerFailureRetainsFrameWitness : Bool := forInitializerFailureRetainsFrame

private def unsupportedIncrementLoud : Bool :=
  let expression : TypedCallableExpression := {
    expression := .increment "??" false (handle "0x10"),
    sourceType := intType, type := intType}
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 0)) with
      body := .block (.return_ expression)}
  match evaluateCallableObject 32 .lp64 callable [signed 7] with
  | .error (.unsupportedOperator "??") => true
  | _ => false

def callableIncrementRefusal : Bool := !unsupportedIncrementLoud

private def unsupportedIncrementPrecedesRead : Bool :=
  let expression : TypedCallableExpression := {
    expression := .increment "??" false (handle "0x99"),
    sourceType := intType, type := intType}
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 0)) with
      body := .block (.return_ expression)}
  match evaluateCallableObject 32 .lp64 callable [signed 7] with
  | .error (.unsupportedOperator "??") => true
  | _ => false

private def unsupportedLogicalLoud : Bool :=
  let one : TypedCallableExpression := {
    expression := .integer 1, sourceType := intType, type := intType}
  let zero : TypedCallableExpression := {
    expression := .integer 0, sourceType := intType, type := intType}
  let expression : TypedCallableExpression := {
    expression := .logical "??" one zero,
    sourceType := intType, type := intType}
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 0)) with
      body := .block (.return_ expression)}
  match evaluateCallableObject 32 .lp64 callable [signed 7] with
  | .ok (.unsupported .unresolvedArithmeticConversions) => true
  | _ => false

private def unsupportedCompoundLoud : Bool :=
  let one : TypedCallableExpression := {
    expression := .integer 1, sourceType := intType, type := intType}
  let zero : TypedCallableExpression := {
    expression := .integer 0, sourceType := intType, type := intType}
  let failingExpression : TypedCallableExpression := {
    expression := .binary "/" one zero,
    sourceType := intType, type := intType}
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 0)) with
      body := .block (.compoundAssign "??" (handle "0x10") failingExpression)}
  match evaluateCallableObject 32 .lp64 callable [signed 7] with
  | .error (.unsupportedOperator "??") => true
  | _ => false

private def unsupportedUnaryLoud : Bool :=
  let one : TypedCallableExpression := {
    expression := .integer 1, sourceType := intType, type := intType}
  let zero : TypedCallableExpression := {
    expression := .integer 0, sourceType := intType, type := intType}
  let failingExpression : TypedCallableExpression := {
    expression := .binary "/" one zero,
    sourceType := intType, type := intType}
  let expression : TypedCallableExpression := {
    expression := .unary "??" failingExpression,
    sourceType := intType, type := intType}
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 0)) with
      body := .block (.return_ expression)}
  match evaluateCallableObject 32 .lp64 callable [signed 7] with
  | .ok (.unsupported .unresolvedArithmeticConversions) => true
  | _ => false

private def unsupportedBinaryLoud : Bool :=
  let missing : TypedCallableExpression := {
    expression := .parameter (handle "0x99"), sourceType := intType, type := intType}
  let one : TypedCallableExpression := {
    expression := .integer 1, sourceType := intType, type := intType}
  let expression : TypedCallableExpression := {
    expression := .binary "??" missing one,
    sourceType := intType, type := intType}
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 0)) with
      body := .block (.return_ expression)}
  match evaluateCallableObject 32 .lp64 callable [signed 7] with
  | .ok (.unsupported .unresolvedArithmeticConversions) => true
  | _ => false

private def switchScopeClosesOnFailure : Bool :=
  let one : TypedCallableExpression := {
    expression := .integer 1, sourceType := intType, type := intType}
  let zero : TypedCallableExpression := {
    expression := .integer 0, sourceType := intType, type := intType}
  let failingExpression : TypedCallableExpression := {
    expression := .binary "/" one zero,
    sourceType := intType, type := intType}
  let clause := .sequence
    (automaticLiteral "0x12" 4) (.expression failingExpression)
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 0)) with
      body := .block (.switch_ one [{label := some 1, body := clause}])}
  match CallableObjectFrame.start .lp64 callable [signed 7] with
  | .ok started =>
      let result := evaluateCallableObjectInFrame 32 started
      result.frame.scopeDepth == 1 && !result.frame.bound (handle "0x12") &&
        match result.result with
        | .ok (.undefined .divisionByZero) => true
        | _ => false
  | .error _ => false

def callableSwitchScopeFailureWitness : Bool := switchScopeClosesOnFailure

private def readsParameter : Bool :=
  match evaluateCallableObject 32 .lp64 (functionWithLocal (.read (handle "0x10"))) [signed 7] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableReadsParameterWitness : Bool := readsParameter

private def valueOnlyRemainsLoud : Bool :=
  match evaluateCallable 32 .lp64 (functionWithLocal (.read (handle "0x10"))) [signed 7] with
  | .error .unsupportedDeclaration => true
  | _ => false

def callableValueOnlyRefusal : Bool := !valueOnlyRemainsLoud

private def selfInitializerRetainsFrame : Bool :=
  match CallableObjectFrame.start .lp64
      (functionWithLocal (.read (handle "0x11"))) [signed 7] with
  | .ok callable =>
      let result := evaluateCallableObjectInFrame 32 callable
      result.frame.bound (handle "0x11") &&
        match result.result with
        | .error (.frameError (.object (.lifetime .lifetimeNotStarted))) => true
        | _ => false
  | .error _ => false

private def nestedBlockDropsLocal : Bool :=
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 3)) with
      body := .block (.sequence
        (.block (.automatic {
          statement := .declare (handle "0x11") intType intType (.literal (signed 3))
          declarations := [handle "0x11"]}))
        (.return_ {
          expression := .integer 0, sourceType := intType, type := intType}))}
  match evaluateCallableObject 32 .lp64 callable [signed 7] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableNestedBlockWitness : Bool := nestedBlockDropsLocal

def callableLoopLocalReentryWitness : Bool := loopLocalReentry

#guard callableLoopLocalReentryWitness

private def parserAdmitsAutomaticLocal : Bool :=
  let declaration := handle "0x11"
  let initializer := handle "0x12"
  let reference : Raw := .object [
    ("id", .string initializer.value), ("kind", .string "DeclRefExpr"),
    ("referencedDecl", .object [
      ("id", .string "0x10"), ("kind", .string "ParmVarDecl")])]
  let statement : Raw := .object [
    ("id", .string "0x20"), ("kind", .string "DeclStmt"),
    ("inner", .array [.object [
      ("id", .string declaration.value), ("kind", .string "VarDecl"),
      ("init", .string "c"), ("inner", .array [reference])]])]
  let localEvidence : CppVariableEvidence := {
    ordinal := 0, occurrence := declaration, canonical := declaration, kind := "VarDecl",
    isLocal := true, localOrParameter := true, storageClass := .none_,
    storageDuration := .automatic, tls := .none_, initStyle := .c,
    initializer := some {
      occurrence := initializer, kind := "DeclRefExpr", sourceType := intType, type := intType},
    isConstexpr := false, attributeCount := 0}
  match parseCallableStatementWithLocals
      {ast := statement, metadata := .null, declarations := []}
      [{ordinal := 0, occurrence := declaration, canonical := declaration, type := intType}]
      [localEvidence] [] none .lp64 intType [parameter] statement with
  | .ok (.automatic admitted, scope) =>
      admitted.declarations == [declaration] &&
        scope.any (fun current => current.declaration == declaration)
  | _ => false

def callableParserAutomaticLocalWitness : Bool := parserAdmitsAutomaticLocal

#guard readsParameter
#guard valueOnlyRemainsLoud
#guard selfInitializerRetainsFrame
#guard nestedBlockDropsLocal
#guard callableNestedBlockWitness
#guard localMutation
#guard callableLocalDeclarationWitness
#guard localIncrement
#guard loopLocalReentry
#guard forBodyFailureRetainsFrame
#guard returnFailureRetainsFrame
#guard forInitializerFailureRetainsFrame
#guard unsupportedIncrementLoud
#guard !callableIncrementRefusal
#guard unsupportedIncrementPrecedesRead
#guard unsupportedLogicalLoud
#guard unsupportedCompoundLoud
#guard unsupportedUnaryLoud
#guard unsupportedBinaryLoud
#guard switchScopeClosesOnFailure
#guard parserAdmitsAutomaticLocal
#guard callableParserAutomaticLocalWitness
#guard callableForBodyFailureRetainsFrameWitness
#guard callableReturnFailureRetainsFrameWitness
#guard callableForInitializerFailureRetainsFrameWitness
#guard callableSwitchScopeFailureWitness
#guard callableReadsParameterWitness
#guard !callableValueOnlyRefusal

theorem callable_local_declaration_witness : callableLocalDeclarationWitness = true := by
  rfl

theorem callable_nested_block_witness : callableNestedBlockWitness = true := by
  rfl

private def incrementFunction (type : CppIntType) (operator : String)
    (isPostfix : Bool) : CallableFunction := {
  occurrence := functionDeclaration
  signature := {result := .builtin type, parameters := [.builtin type], variadic := false}
  parameters := [{parameter with type := .builtin type}]
  body := .return_ {
    expression := .increment operator isPostfix (handle "0x10")
    sourceType := .builtin type, type := .builtin type}
}

private def checkIncrement (type : CppIntType) (operator : String) (isPostfix : Bool)
    (argument expected : IntegralValue) : Bool :=
  let function := incrementFunction type operator isPostfix
  (evaluateCallableObject 16 .lp64 function [argument]).toOption == some (.ok expected) &&
    (evaluateCallable 16 .lp64 function [argument]).toOption == some (.ok expected)

#guard checkIncrement .short "++" false ⟨.signed 16, 32767⟩ ⟨.signed 16, -32768⟩
#guard checkIncrement .short "++" true ⟨.signed 16, 32767⟩ ⟨.signed 16, 32767⟩
#guard checkIncrement .short "--" false ⟨.signed 16, -32768⟩ ⟨.signed 16, 32767⟩
#guard checkIncrement .short "--" true ⟨.signed 16, -32768⟩ ⟨.signed 16, -32768⟩
#guard checkIncrement .signedChar "++" false ⟨.signed 8, 127⟩ ⟨.signed 8, -128⟩
#guard checkIncrement .signedChar "--" false ⟨.signed 8, -128⟩ ⟨.signed 8, 127⟩
#guard checkIncrement .unsignedChar "++" false ⟨.unsigned 8, 255⟩ ⟨.unsigned 8, 0⟩
#guard checkIncrement .unsignedShort "--" false ⟨.unsigned 16, 0⟩ ⟨.unsigned 16, 65535⟩
#guard checkIncrement .unsignedInt "++" false ⟨.unsigned 32, 4294967295⟩ ⟨.unsigned 32, 0⟩
#guard checkIncrement .unsignedLongLong "--" false
  ⟨.unsigned 64, 0⟩ ⟨.unsigned 64, 18446744073709551615⟩

-- A discarded postfix expression must still store the converted result.
private def postfixStore : Bool :=
  let function := incrementFunction .short "++" true
  let function := {function with body := match function.body with
    | .return_ expression => .expression expression
    | other => other}
  match CallableObjectFrame.start .lp64 function [⟨.signed 16, 32767⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 16 started
      (outcome.result matches .error .missingReturn) &&
        (outcome.frame.read (handle "0x10")).result.toOption == some ⟨.signed 16, -32768⟩

-- No native oracle execution is run for signed overflow. The failed arithmetic
-- leaves the live parameter unchanged in both prefix and postfix cases.
private def overflowRetainsParameter (operator : String) (isPostfix : Bool) (value : Int) : Bool :=
  match CallableObjectFrame.start .lp64 (incrementFunction .int operator isPostfix) [signed value] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 16 started
      outcome.result.toOption == some (.undefined .signedOverflow) &&
        (outcome.frame.read (handle "0x10")).result.toOption == some (signed value)

#guard postfixStore
#guard overflowRetainsParameter "++" false 2147483647
#guard overflowRetainsParameter "++" true 2147483647
#guard overflowRetainsParameter "--" false (-2147483648)
#guard overflowRetainsParameter "--" true (-2147483648)

-- The execution boundary must reduce in the kernel as well as run natively.
example (callable : CallableObjectFrame) :
    evaluateCallableObjectInFrame 0 callable =
      {frame := callable.frame, result := .error (.frameError .fuelExhausted)} := rfl

private theorem kernelObjectExecution :
    (localMutation && localIncrement && loopLocalReentry && forBodyFailureRetainsFrame &&
      switchScopeClosesOnFailure && postfixStore &&
      overflowRetainsParameter "++" true 2147483647) = true := rfl

#print axioms kernelObjectExecution
#print axioms callable_local_declaration_witness
#print axioms callable_nested_block_witness

private def kernelControl (loop : CallableStatement) : Bool :=
  let function : CallableFunction := {
    occurrence := functionDeclaration
    signature := {result := intType, parameters := [intType], variadic := false}
    parameters := [parameter]
    body := .block (.sequence loop (.return_ {
      expression := .parameter (handle "0x10"), sourceType := intType, type := intType}))}
  (evaluateCallable 64 .lp64 function [signed 3]).toOption == some (.ok (signed 0)) &&
    (evaluateCallableObject 64 .lp64 function [signed 3]).toOption == some (.ok (signed 0))

private def controlParameter : TypedCallableExpression := {
  expression := .parameter (handle "0x10"), sourceType := intType, type := intType}

private def controlStep : CallableStatement := .expression {
  expression := .increment "--" false (handle "0x10"), sourceType := intType, type := intType}

private theorem kernelControlExecution :
    (kernelControl (.doWhile controlStep controlParameter) &&
      kernelControl (.forLoop .skip controlParameter controlStep
        (.switch_ controlParameter [
          {label := some 3, body := .continue_},
          {label := some 2, body := .skip},
          {label := none, body := .break_}])) &&
      checkIncrement .short "++" false ⟨.signed 16, 32767⟩ ⟨.signed 16, -32768⟩) = true := rfl

#print axioms kernelControlExecution

end LeanModels.Cpp.CallableObjectEvaluationTests
