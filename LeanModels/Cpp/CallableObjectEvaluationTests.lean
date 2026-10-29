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

def callableIncrementPrecedesReadRefusal : Bool := !unsupportedIncrementPrecedesRead

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

def callableLogicalRefusal : Bool := !unsupportedLogicalLoud

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

def callableCompoundRefusal : Bool := !unsupportedCompoundLoud

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

def callableUnaryRefusal : Bool := !unsupportedUnaryLoud

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

def callableBinaryRefusal : Bool := !unsupportedBinaryLoud

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

def callableSelfInitializerFailureWitness : Bool := selfInitializerRetainsFrame

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
#guard !callableLogicalRefusal
#guard !callableCompoundRefusal
#guard !callableUnaryRefusal
#guard !callableBinaryRefusal
#guard !callableIncrementPrecedesReadRefusal
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

private def logicalFrame : Bool :=
  let base := incrementFunction .int "++" false
  let left : TypedCallableExpression := {
    expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
  let right : TypedCallableExpression := {
    expression := .increment "++" false (handle "0x10"),
    sourceType := intType, type := intType}
  let logical : TypedCallableExpression := {
    expression := .logical "&&" left right,
    sourceType := .builtin .boolean, type := .builtin .boolean}
  let function := {base with body := .block (.return_ {
    expression := .comma logical left,
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 0],
      evaluateCallableObject 32 .lp64 function [signed 1] with
  | .ok (.ok zero), .ok (.ok one) => zero == signed 0 && one == signed 2
  | _, _ => false

def callableLogicalFrameWitness : Bool := logicalFrame

#guard callableLogicalFrameWitness

private def logicalOrFrame : Bool :=
  let base := incrementFunction .int "++" false
  let left : TypedCallableExpression := {
    expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
  let right : TypedCallableExpression := {
    expression := .increment "++" false (handle "0x10"),
    sourceType := intType, type := intType}
  let logical : TypedCallableExpression := {
    expression := .logical "||" left right,
    sourceType := .builtin .boolean, type := .builtin .boolean}
  let function := {base with body := .block (.return_ {
    expression := .comma logical left,
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 1],
      evaluateCallableObject 32 .lp64 function [signed 0] with
  | .ok (.ok one), .ok (.ok zero) => one == signed 1 && zero == signed 1
  | _, _ => false

def callableLogicalOrFrameWitness : Bool := logicalOrFrame

#guard callableLogicalOrFrameWitness

private def conditionalFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
  let whenTrue : TypedCallableExpression := {
    expression := .increment "++" false (handle "0x10"),
    sourceType := intType, type := intType}
  let whenFalse := condition
  let selected : TypedCallableExpression := {
    expression := .conditional condition whenTrue whenFalse,
    sourceType := intType, type := intType}
  let function := {base with body := .block (.return_ {
    expression := .comma selected condition,
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 1],
      evaluateCallableObject 32 .lp64 function [signed 0] with
  | .ok (.ok one), .ok (.ok zero) => one == signed 2 && zero == signed 0
  | _, _ => false

def callableConditionalFrameWitness : Bool := conditionalFrame

#guard callableConditionalFrameWitness

private def commaFrame : Bool :=
  let base := incrementFunction .int "++" false
  let left : TypedCallableExpression := {
    expression := .increment "++" false (handle "0x10"),
    sourceType := intType, type := intType}
  let right : TypedCallableExpression := {
    expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
  let function := {base with body := .block (.return_ {
    expression := .comma left right,
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 4] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableCommaFrameWitness : Bool := commaFrame

#guard callableCommaFrameWitness

private def assignmentFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.assign (handle "0x10")
      {expression := .integer 7, sourceType := intType, type := intType})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := intType, type := intType}))}
  match evaluateCallableObject 32 .lp64 function [signed 4] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableAssignmentFrameWitness : Bool := assignmentFrame

#guard callableAssignmentFrameWitness

private def unaryMinusFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .unary "-"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed (-7)] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableUnaryMinusFrameWitness : Bool := unaryMinusFrame

#guard callableUnaryMinusFrameWitness

private def unaryComplementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .unary "~"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed (-1)] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableUnaryComplementFrameWitness : Bool := unaryComplementFrame

#guard callableUnaryComplementFrameWitness

private def unaryLogicalNotFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with
    signature := {result := .builtin .boolean, parameters := [.builtin .int], variadic := false}
    body := .block (.return_ {
      expression := .unary "!"
        {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      sourceType := .builtin .boolean, type := .builtin .boolean})}
  match evaluateCallableObject 32 .lp64 function [signed 0],
      evaluateCallableObject 32 .lp64 function [signed 3] with
  | .ok (.ok zero), .ok (.ok nonzero) =>
      zero == ⟨.boolean, 1⟩ && nonzero == ⟨.boolean, 0⟩
  | _, _ => false

def callableUnaryLogicalNotFrameWitness : Bool := unaryLogicalNotFrame

#guard callableUnaryLogicalNotFrameWitness

private def unaryPlusFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .unary "+"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed (-7)] with
  | .ok (.ok value) => value == signed (-7)
  | _ => false

def callableUnaryPlusFrameWitness : Bool := unaryPlusFrame

#guard callableUnaryPlusFrameWitness

private def binaryAddFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .binary "+"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 5, sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 12
  | _ => false

def callableBinaryAddFrameWitness : Bool := binaryAddFrame

#guard callableBinaryAddFrameWitness

private def binarySubtractFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .binary "-"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 7, sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 12] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableBinarySubtractFrameWitness : Bool := binarySubtractFrame

#guard callableBinarySubtractFrameWitness

private def binaryMultiplyFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .binary "*"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 4, sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 3] with
  | .ok (.ok value) => value == signed 12
  | _ => false

def callableBinaryMultiplyFrameWitness : Bool := binaryMultiplyFrame

#guard callableBinaryMultiplyFrameWitness

private def binaryDivideFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .binary "/"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 12] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableBinaryDivideFrameWitness : Bool := binaryDivideFrame

#guard callableBinaryDivideFrameWitness

private def binaryRemainderFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .binary "%"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 5, sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 13] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableBinaryRemainderFrameWitness : Bool := binaryRemainderFrame

#guard callableBinaryRemainderFrameWitness

private def binaryBitAndFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .binary "&"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 13] with
  | .ok (.ok value) => value == signed 1
  | _ => false

def callableBinaryBitAndFrameWitness : Bool := binaryBitAndFrame

#guard callableBinaryBitAndFrameWitness

private def binaryBitOrFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .binary "|"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 12] with
  | .ok (.ok value) => value == signed 15
  | _ => false

def callableBinaryBitOrFrameWitness : Bool := binaryBitOrFrame

#guard callableBinaryBitOrFrameWitness

private def binaryBitXorFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .binary "^"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 13] with
  | .ok (.ok value) => value == signed 14
  | _ => false

def callableBinaryBitXorFrameWitness : Bool := binaryBitXorFrame

#guard callableBinaryBitXorFrameWitness

private def binaryShiftLeftFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .binary "<<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 4, sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 16
  | _ => false

def callableBinaryShiftLeftFrameWitness : Bool := binaryShiftLeftFrame

#guard callableBinaryShiftLeftFrameWitness

private def binaryShiftRightFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.return_ {
    expression := .binary ">>"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType, type := intType})}
  match evaluateCallableObject 32 .lp64 function [signed (-7)] with
  | .ok (.ok value) => value == signed (-4)
  | _ => false

def callableBinaryShiftRightFrameWitness : Bool := binaryShiftRightFrame

#guard callableBinaryShiftRightFrameWitness

private def binaryLessThanFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with
    signature := {result := .builtin .boolean, parameters := [.builtin .int], variadic := false}
    body := .block (.return_ {
      expression := .binary "<"
        {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
        {expression := .integer 5, sourceType := intType, type := intType}
      sourceType := .builtin .boolean, type := .builtin .boolean})}
  match evaluateCallableObject 32 .lp64 function [signed 3] with
  | .ok (.ok value) => value == ⟨.boolean, 1⟩
  | _ => false

def callableBinaryLessThanFrameWitness : Bool := binaryLessThanFrame

#guard callableBinaryLessThanFrameWitness

private def binaryLessEqualFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with
    signature := {result := .builtin .boolean, parameters := [.builtin .int], variadic := false}
    body := .block (.return_ {
      expression := .binary "<="
        {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
        {expression := .integer 5, sourceType := intType, type := intType}
      sourceType := .builtin .boolean, type := .builtin .boolean})}
  match evaluateCallableObject 32 .lp64 function [signed 5] with
  | .ok (.ok value) => value == ⟨.boolean, 1⟩
  | _ => false

def callableBinaryLessEqualFrameWitness : Bool := binaryLessEqualFrame

#guard callableBinaryLessEqualFrameWitness

private def binaryEqualFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with
    signature := {result := .builtin .boolean, parameters := [.builtin .int], variadic := false}
    body := .block (.return_ {
      expression := .binary "=="
        {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
        {expression := .integer 5, sourceType := intType, type := intType}
      sourceType := .builtin .boolean, type := .builtin .boolean})}
  match evaluateCallableObject 32 .lp64 function [signed 5] with
  | .ok (.ok value) => value == ⟨.boolean, 1⟩
  | _ => false

def callableBinaryEqualFrameWitness : Bool := binaryEqualFrame

#guard callableBinaryEqualFrameWitness

private def binaryNotEqualFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with
    signature := {result := .builtin .boolean, parameters := [.builtin .int], variadic := false}
    body := .block (.return_ {
      expression := .binary "!="
        {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
        {expression := .integer 5, sourceType := intType, type := intType}
      sourceType := .builtin .boolean, type := .builtin .boolean})}
  match evaluateCallableObject 32 .lp64 function [signed 6] with
  | .ok (.ok value) => value == ⟨.boolean, 1⟩
  | _ => false

def callableBinaryNotEqualFrameWitness : Bool := binaryNotEqualFrame

#guard callableBinaryNotEqualFrameWitness

private def binaryGreaterThanFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with
    signature := {result := .builtin .boolean, parameters := [.builtin .int], variadic := false}
    body := .block (.return_ {
      expression := .binary ">"
        {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
        {expression := .integer 5, sourceType := intType, type := intType}
      sourceType := .builtin .boolean, type := .builtin .boolean})}
  match evaluateCallableObject 32 .lp64 function [signed 6] with
  | .ok (.ok value) => value == ⟨.boolean, 1⟩
  | _ => false

def callableBinaryGreaterThanFrameWitness : Bool := binaryGreaterThanFrame

#guard callableBinaryGreaterThanFrameWitness

private def binaryGreaterEqualFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with
    signature := {result := .builtin .boolean, parameters := [.builtin .int], variadic := false}
    body := .block (.return_ {
      expression := .binary ">="
        {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
        {expression := .integer 5, sourceType := intType, type := intType}
      sourceType := .builtin .boolean, type := .builtin .boolean})}
  match evaluateCallableObject 32 .lp64 function [signed 5] with
  | .ok (.ok value) => value == ⟨.boolean, 1⟩
  | _ => false

def callableBinaryGreaterEqualFrameWitness : Bool := binaryGreaterEqualFrame

#guard callableBinaryGreaterEqualFrameWitness

private def sizeOfFrame : Bool :=
  let function : CallableFunction := {
    occurrence := functionDeclaration
    signature := {result := unsignedLongType, parameters := [], variadic := false}
    parameters := []
    body := .block (.return_ {
      expression := .sizeOf shortType
      sourceType := unsignedLongType
      type := unsignedLongType})}
  match evaluateCallableObject 32 .lp64 function [] with
  | .ok (.ok value) => value == ⟨.unsigned 64, 2⟩
  | _ => false

def callableSizeOfFrameWitness : Bool := sizeOfFrame

#guard callableSizeOfFrameWitness

private def alignOfFrame : Bool :=
  let function : CallableFunction := {
    occurrence := functionDeclaration
    signature := {result := unsignedLongType, parameters := [], variadic := false}
    parameters := []
    body := .block (.return_ {
      expression := .alignOf shortType
      sourceType := unsignedLongType
      type := unsignedLongType})}
  match evaluateCallableObject 32 .lp64 function [] with
  | .ok (.ok value) => value == ⟨.unsigned 64, 2⟩
  | _ => false

def callableAlignOfFrameWitness : Bool := alignOfFrame

#guard callableAlignOfFrameWitness

private def integralCastFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with
    signature := {result := intType, parameters := [.builtin .short], variadic := false}
    body := .block (.return_ {
      expression := .convert {
        expression := .parameter (handle "0x10")
        sourceType := .builtin .short
        type := .builtin .short}
      sourceType := .builtin .short
      type := intType})}
  match evaluateCallableObject 32 .lp64 function [⟨.signed 16, -7⟩] with
  | .ok (.ok value) => value == signed (-7)
  | _ => false

def callableIntegralCastFrameWitness : Bool := integralCastFrame

#guard callableIntegralCastFrameWitness

private def narrowIntegralCastFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with
    signature := {result := .builtin .unsignedChar, parameters := [.builtin .short], variadic := false}
    body := .block (.return_ {
      expression := .convert {
        expression := .parameter (handle "0x10")
        sourceType := .builtin .short
        type := .builtin .short}
      sourceType := .builtin .short
      type := .builtin .unsignedChar})}
  match evaluateCallableObject 32 .lp64 function [⟨.signed 16, -7⟩] with
  | .ok (.ok value) => value == ⟨.unsigned 8, 249⟩
  | _ => false

def callableNarrowIntegralCastFrameWitness : Bool := narrowIntegralCastFrame

#guard callableNarrowIntegralCastFrameWitness

private def noexceptFrame : Bool :=
  let base := incrementFunction .int "++" false
  let operand : TypedCallableExpression := {
    expression := .binary "+"
      {expression := .integer 1, sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType, type := intType}
  let function := {base with
    signature := {result := .builtin .boolean, parameters := [.builtin .int], variadic := false}
    body := .block (.return_ {
      expression := .noexceptExpr operand
      sourceType := .builtin .boolean
      type := .builtin .boolean})}
  match evaluateCallableObject 32 .lp64 function [signed 0] with
  | .ok (.ok value) => value == ⟨.boolean, 1⟩
  | _ => false

def callableNoexceptFrameWitness : Bool := noexceptFrame

#guard callableNoexceptFrameWitness

private def boolLiteralFrame : Bool :=
  let function : CallableFunction := {
    occurrence := functionDeclaration
    signature := {result := .builtin .boolean, parameters := [], variadic := false}
    parameters := []
    body := .block (.return_ {
      expression := .integer 1
      sourceType := .builtin .boolean
      type := .builtin .boolean})}
  match evaluateCallableObject 32 .lp64 function [] with
  | .ok (.ok value) => value == ⟨.boolean, 1⟩
  | _ => false

def callableBoolLiteralFrameWitness : Bool := boolLiteralFrame

#guard callableBoolLiteralFrameWitness

private def nullComparisonFrame : Bool :=
  let function : CallableFunction := {
    occurrence := functionDeclaration
    signature := {result := .builtin .boolean, parameters := [], variadic := false}
    parameters := []
    body := .block (.return_ {
      expression := .nullComparison "=="
      sourceType := .builtin .boolean
      type := .builtin .boolean})}
  match evaluateCallableObject 32 .lp64 function [] with
  | .ok (.ok value) => value == ⟨.boolean, 1⟩
  | _ => false

def callableNullComparisonFrameWitness : Bool := nullComparisonFrame

#guard callableNullComparisonFrameWitness

private def nullInequalityFrame : Bool :=
  let function : CallableFunction := {
    occurrence := functionDeclaration
    signature := {result := .builtin .boolean, parameters := [], variadic := false}
    parameters := []
    body := .block (.return_ {
      expression := .nullComparison "!="
      sourceType := .builtin .boolean
      type := .builtin .boolean})}
  match evaluateCallableObject 32 .lp64 function [] with
  | .ok (.ok value) => value == ⟨.boolean, 0⟩
  | _ => false

def callableNullInequalityFrameWitness : Bool := nullInequalityFrame

#guard callableNullInequalityFrameWitness

private def integerLiteralFrame : Bool :=
  let function : CallableFunction := {
    occurrence := functionDeclaration
    signature := {result := intType, parameters := [], variadic := false}
    parameters := []
    body := .block (.return_ {
      expression := .integer 42
      sourceType := intType
      type := intType})}
  match evaluateCallableObject 32 .lp64 function [] with
  | .ok (.ok value) => value == signed 42
  | _ => false

def callableIntegerLiteralFrameWitness : Bool := integerLiteralFrame

#guard callableIntegerLiteralFrameWitness

private def unsignedIntegerLiteralFrame : Bool :=
  let function : CallableFunction := {
    occurrence := functionDeclaration
    signature := {result := .builtin .unsignedInt, parameters := [], variadic := false}
    parameters := []
    body := .block (.return_ {
      expression := .integer 7
      sourceType := .builtin .unsignedInt
      type := .builtin .unsignedInt})}
  match evaluateCallableObject 32 .lp64 function [] with
  | .ok (.ok value) => value == ⟨.unsigned 32, 7⟩
  | _ => false

def callableUnsignedIntegerLiteralFrameWitness : Bool := unsignedIntegerLiteralFrame

#guard callableUnsignedIntegerLiteralFrameWitness

private def conditionalStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let whenTrue : CallableStatement := .return_ {
    expression := .integer 7
    sourceType := intType
    type := intType}
  let whenFalse : CallableStatement := .return_ {
    expression := .integer 3
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.conditional condition whenTrue whenFalse)}
  match evaluateCallableObject 32 .lp64 function [signed 1],
      evaluateCallableObject 32 .lp64 function [signed 0] with
  | .ok (.ok one), .ok (.ok zero) => one == signed 7 && zero == signed 3
  | _, _ => false

def callableConditionalStatementFrameWitness : Bool := conditionalStatementFrame

#guard callableConditionalStatementFrameWitness

private def whileStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let step : CallableStatement := .expression {
    expression := .increment "--" false (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.whileLoop condition step)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 3] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableWhileStatementFrameWitness : Bool := whileStatementFrame

#guard callableWhileStatementFrameWitness

private def switchStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let one : CallableStatement := .return_ {
    expression := .integer 7
    sourceType := intType
    type := intType}
  let other : CallableStatement := .return_ {
    expression := .integer 3
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.switch_ condition [
    {label := some 1, body := one},
    {label := none, body := other}])}
  match evaluateCallableObject 64 .lp64 function [signed 1],
      evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok oneValue), .ok (.ok otherValue) =>
      oneValue == signed 7 && otherValue == signed 3
  | _, _ => false

def callableSwitchStatementFrameWitness : Bool := switchStatementFrame

#guard callableSwitchStatementFrameWitness

private def forStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let step : CallableStatement := .expression {
    expression := .increment "--" false (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.forLoop .skip condition step .skip)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 3] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableForStatementFrameWitness : Bool := forStatementFrame

#guard callableForStatementFrameWitness

private def breakContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let increment : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .sequence increment (.sequence .break_ .continue_)
  let function := {base with body := .block (.sequence
    (.whileLoop condition body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 1
  | _ => false

def callableBreakContinueStatementFrameWitness : Bool := breakContinueStatementFrame

#guard callableBreakContinueStatementFrameWitness

private def gotoStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let replacement : TypedCallableExpression := {
    expression := .integer 7
    sourceType := intType
    type := intType}
  let result : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.conditional condition (.goto_ "done") .skip)
    (.sequence
      (.assign (handle "0x10") replacement)
      (.label "done" (.return_ result))))}
  match evaluateCallableObject 32 .lp64 function [signed 1],
      evaluateCallableObject 32 .lp64 function [signed 0] with
  | .ok (.ok one), .ok (.ok zero) => one == signed 1 && zero == signed 7
  | _, _ => false

def callableGotoStatementFrameWitness : Bool := gotoStatementFrame

#guard callableGotoStatementFrameWitness

private def nullStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    .skip
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 32 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableNullStatementFrameWitness : Bool := nullStatementFrame

#guard callableNullStatementFrameWitness

private def returnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let returned : TypedCallableExpression := {
    expression := .integer 11
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.return_ returned)}
  match evaluateCallableObject 32 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 11
  | _ => false

def callableReturnStatementFrameWitness : Bool := returnStatementFrame

#guard callableReturnStatementFrameWitness

private def doWhileStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "--" false (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.doWhile step condition)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 3],
      evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok three), .ok (.ok zero) => three == signed 0 && zero == signed (-1)
  | _, _ => false

def callableDoWhileStatementFrameWitness : Bool := doWhileStatementFrame

#guard callableDoWhileStatementFrameWitness

private def compoundAssignStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let amount : TypedCallableExpression := {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10") amount)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 32 .lp64 function [signed 5] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableCompoundAssignStatementFrameWitness : Bool := compoundAssignStatementFrame

#guard callableCompoundAssignStatementFrameWitness

private def blockScopeStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.block (automaticLiteral "0x11" 3))
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 32 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableBlockScopeStatementFrameWitness : Bool := blockScopeStatementFrame

#guard callableBlockScopeStatementFrameWitness

private def voidReturnStatementFrame : Bool :=
  let function : CallableFunction := {
    occurrence := functionDeclaration
    signature := {result := .void, parameters := [intType], variadic := false}
    parameters := [parameter]
    body := .block .returnVoid}
  match evaluateCallableObjectResult 32 .lp64 function [signed 7] with
  | .ok (.ok none) => true
  | _ => false

def callableVoidReturnStatementFrameWitness : Bool := voidReturnStatementFrame

#guard callableVoidReturnStatementFrameWitness

private def conditionalNoElseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let replacement : TypedCallableExpression := {
    expression := .integer 9
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.conditional condition (.assign (handle "0x10") replacement) .skip)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 32 .lp64 function [signed 1],
      evaluateCallableObject 32 .lp64 function [signed 0] with
  | .ok (.ok one), .ok (.ok zero) => one == signed 9 && zero == signed 0
  | _, _ => false

def callableConditionalNoElseStatementFrameWitness : Bool := conditionalNoElseStatementFrame

#guard callableConditionalNoElseStatementFrameWitness

private def switchFallthroughStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let five : TypedCallableExpression := {
    expression := .integer 5
    sourceType := intType
    type := intType}
  let two : TypedCallableExpression := {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .assign (handle "0x10") five},
      {label := some 2, body := .compoundAssign "+=" (handle "0x10") two},
      {label := none, body := .break_}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1],
      evaluateCallableObject 64 .lp64 function [signed 2],
      evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok one), .ok (.ok twoValue), .ok (.ok zero) =>
      one == signed 7 && twoValue == signed 4 && zero == signed 0
  | _, _, _ => false

def callableSwitchFallthroughStatementFrameWitness : Bool := switchFallthroughStatementFrame

#guard callableSwitchFallthroughStatementFrameWitness

private def whileZeroIterationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let replacement : TypedCallableExpression := {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.whileLoop condition (.assign (handle "0x10") replacement))
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 32 .lp64 function [signed 1],
      evaluateCallableObject 32 .lp64 function [signed 2] with
  | .ok (.ok one), .ok (.ok two) => one == signed 1 && two == signed 0
  | _, _ => false

def callableWhileZeroIterationStatementFrameWitness : Bool := whileZeroIterationStatementFrame

#guard callableWhileZeroIterationStatementFrameWitness

private def forInitializerBodyStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body : CallableStatement := .compoundAssign "+=" (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.forLoop initializer condition step body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableForInitializerBodyStatementFrameWitness : Bool := forInitializerBodyStatementFrame

#guard callableForInitializerBodyStatementFrameWitness

private def forContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.forLoop initializer condition step .continue_)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableForContinueStatementFrameWitness : Bool := forContinueStatementFrame

#guard callableForContinueStatementFrameWitness

private def forBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.forLoop initializer condition step .break_)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableForBreakStatementFrameWitness : Bool := forBreakStatementFrame

#guard callableForBreakStatementFrameWitness

private def doWhileContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .sequence
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType})
    .continue_
  let function := {base with body := .block (.sequence
    (.doWhile body condition)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableDoWhileContinueStatementFrameWitness : Bool := doWhileContinueStatementFrame

#guard callableDoWhileContinueStatementFrameWitness

private def whileContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .sequence
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType})
    .continue_
  let function := {base with body := .block (.sequence
    (.whileLoop condition body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableWhileContinueStatementFrameWitness : Bool := whileContinueStatementFrame

#guard callableWhileContinueStatementFrameWitness

private def localDeclarationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDeclarationStatementFrameWitness : Bool := localDeclarationStatementFrame

#guard callableLocalDeclarationStatementFrameWitness

private def localIncrementStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.expression {
        expression := .increment "++" false (handle "0x11")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalIncrementStatementFrameWitness : Bool := localIncrementStatementFrame

#guard callableLocalIncrementStatementFrameWitness

private def localAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.assign (handle "0x11") {
        expression := .integer 7
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableLocalAssignmentStatementFrameWitness : Bool := localAssignmentStatementFrame

#guard callableLocalAssignmentStatementFrameWitness

private def localCompoundAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.compoundAssign "+=" (handle "0x11") {
        expression := .integer 4
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableLocalCompoundAssignmentStatementFrameWitness : Bool :=
  localCompoundAssignmentStatementFrame

#guard callableLocalCompoundAssignmentStatementFrameWitness

private def localPostIncrementStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.expression {
        expression := .increment "++" true (handle "0x11")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalPostIncrementStatementFrameWitness : Bool :=
  localPostIncrementStatementFrame

#guard callableLocalPostIncrementStatementFrameWitness

private def localDecrementStatementFrame : Bool :=
  let base := incrementFunction .int "--" false
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.expression {
        expression := .increment "--" false (handle "0x11")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 2
  | _ => false

def callableLocalDecrementStatementFrameWitness : Bool := localDecrementStatementFrame

#guard callableLocalDecrementStatementFrameWitness

private def localPostDecrementStatementFrame : Bool :=
  let base := incrementFunction .int "--" false
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.expression {
        expression := .increment "--" true (handle "0x11")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 2
  | _ => false

def callableLocalPostDecrementStatementFrameWitness : Bool :=
  localPostDecrementStatementFrame

#guard callableLocalPostDecrementStatementFrameWitness

private def localParameterInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : Expression := .read (handle "0x10")
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType initializer
      declarations := [handle "0x11"]})
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableLocalParameterInitializationStatementFrameWitness : Bool :=
  localParameterInitializationStatementFrame

#guard callableLocalParameterInitializationStatementFrameWitness

private def localComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : Expression :=
    .binary .add (.read (handle "0x10")) (.literal (signed 1))
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType initializer
      declarations := [handle "0x11"]})
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 8
  | _ => false

def callableLocalComputedInitializationStatementFrameWitness : Bool :=
  localComputedInitializationStatementFrame

#guard callableLocalComputedInitializationStatementFrameWitness

private def localChainedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let secondInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 4))
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.automatic {
        statement := .declare (handle "0x12") intType intType secondInitializer
        declarations := [handle "0x12"]})
      (.return_ {
        expression := .parameter (handle "0x12")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableLocalChainedInitializationStatementFrameWitness : Bool :=
  localChainedInitializationStatementFrame

#guard callableLocalChainedInitializationStatementFrameWitness

private def localShadowStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType (.literal (signed 4))
          declarations := [handle "0x12"]})
        .skip))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalShadowStatementFrameWitness : Bool := localShadowStatementFrame

#guard callableLocalShadowStatementFrameWitness

private def localNestedAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.block (.assign (handle "0x11") {
        expression := .integer 5
        sourceType := intType
        type := intType}))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalNestedAssignmentStatementFrameWitness : Bool :=
  localNestedAssignmentStatementFrame

#guard callableLocalNestedAssignmentStatementFrameWitness

private def localNestedCompoundAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.block (.compoundAssign "+=" (handle "0x11") {
        expression := .integer 2
        sourceType := intType
        type := intType}))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalNestedCompoundAssignmentStatementFrameWitness : Bool :=
  localNestedCompoundAssignmentStatementFrame

#guard callableLocalNestedCompoundAssignmentStatementFrameWitness

private def localNestedIncrementStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.block (.expression {
        expression := .increment "++" false (handle "0x11")
        sourceType := intType
        type := intType}))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalNestedIncrementStatementFrameWitness : Bool :=
  localNestedIncrementStatementFrame

#guard callableLocalNestedIncrementStatementFrameWitness

private def localNestedPostIncrementStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.block (.expression {
        expression := .increment "++" true (handle "0x11")
        sourceType := intType
        type := intType}))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalNestedPostIncrementStatementFrameWitness : Bool :=
  localNestedPostIncrementStatementFrame

#guard callableLocalNestedPostIncrementStatementFrameWitness

private def localNestedDecrementStatementFrame : Bool :=
  let base := incrementFunction .int "--" false
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.block (.expression {
        expression := .increment "--" false (handle "0x11")
        sourceType := intType
        type := intType}))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 2
  | _ => false

def callableLocalNestedDecrementStatementFrameWitness : Bool :=
  localNestedDecrementStatementFrame

#guard callableLocalNestedDecrementStatementFrameWitness

private def localNestedPostDecrementStatementFrame : Bool :=
  let base := incrementFunction .int "--" false
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.block (.expression {
        expression := .increment "--" true (handle "0x11")
        sourceType := intType
        type := intType}))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 2
  | _ => false

def callableLocalNestedPostDecrementStatementFrameWitness : Bool :=
  localNestedPostDecrementStatementFrame

#guard callableLocalNestedPostDecrementStatementFrameWitness

private def localNestedComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType initializer
          declarations := [handle "0x12"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x12")
          sourceType := intType
          type := intType})))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalNestedComputedInitializationStatementFrameWitness : Bool :=
  localNestedComputedInitializationStatementFrame

#guard callableLocalNestedComputedInitializationStatementFrameWitness

private def localNestedShadowComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let outerInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let innerInitializer : Expression :=
    .binary .add (.read (handle "0x12")) (.literal (signed 1))
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType outerInitializer
          declarations := [handle "0x12"]})
        (.block (.automatic {
          statement := .declare (handle "0x13") intType intType innerInitializer
          declarations := [handle "0x13"]
        }))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 128 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationStatementFrame

#guard callableLocalNestedShadowComputedInitializationStatementFrameWitness

private def localNestedShadowComputedInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let outerInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let innerInitializer : Expression :=
    .binary .add (.read (handle "0x12")) (.literal (signed 1))
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.block (.sequence
      (.automatic {
        statement := .declare (handle "0x12") intType intType outerInitializer
        declarations := [handle "0x12"]})
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType innerInitializer
          declarations := [handle "0x13"]})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))))) }
  match evaluateCallableObject 128 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationReturnStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationReturnStatementFrame

#guard callableLocalNestedShadowComputedInitializationReturnStatementFrameWitness

private def localNestedShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let outerInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let innerInitializer : Expression :=
    .binary .add (.read (handle "0x12")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType outerInitializer
          declarations := [handle "0x12"]})
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType innerInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 6
  | _ => false

def callableLocalNestedShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalNestedShadowComputedInitializationAssignmentStatementFrameWitness

private def localNestedShadowComputedInitializationContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.whileLoop condition loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationContinueStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationContinueStatementFrame

#guard callableLocalNestedShadowComputedInitializationContinueStatementFrameWitness

private def localNestedShadowComputedInitializationBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.whileLoop condition loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationBreakStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationBreakStatementFrame

#guard callableLocalNestedShadowComputedInitializationBreakStatementFrameWitness

private def localNestedShadowComputedInitializationWhileStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.whileLoop condition loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationWhileStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationWhileStatementFrame

#guard callableLocalNestedShadowComputedInitializationWhileStatementFrameWitness

private def localNestedShadowComputedInitializationWhileContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.whileLoop condition loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationWhileContinueStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationWhileContinueStatementFrame

#guard callableLocalNestedShadowComputedInitializationWhileContinueStatementFrameWitness

private def localNestedShadowComputedInitializationWhileBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.whileLoop condition loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationWhileBreakStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationWhileBreakStatementFrame

#guard callableLocalNestedShadowComputedInitializationWhileBreakStatementFrameWitness

private def localNestedShadowComputedInitializationWhileReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.whileLoop condition loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationWhileReturnStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationWhileReturnStatementFrame

#guard callableLocalNestedShadowComputedInitializationWhileReturnStatementFrameWitness

private def localNestedShadowComputedInitializationWhileAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.whileLoop condition loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 6
  | _ => false

def callableLocalNestedShadowComputedInitializationWhileAssignmentStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationWhileAssignmentStatementFrame

#guard callableLocalNestedShadowComputedInitializationWhileAssignmentStatementFrameWitness

private def localNestedShadowComputedInitializationWhileAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.whileLoop condition loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationWhileAssignmentFalseStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationWhileAssignmentFalseStatementFrame

#guard callableLocalNestedShadowComputedInitializationWhileAssignmentFalseStatementFrameWitness

private def localNestedShadowComputedInitializationWhileFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.whileLoop condition loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationWhileFalseStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationWhileFalseStatementFrame

#guard callableLocalNestedShadowComputedInitializationWhileFalseStatementFrameWitness

private def localNestedShadowComputedInitializationDoWhileStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.doWhile loopBody condition)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationDoWhileStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationDoWhileStatementFrame

#guard callableLocalNestedShadowComputedInitializationDoWhileStatementFrameWitness

private def localNestedShadowComputedInitializationDoWhileAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.doWhile loopBody condition)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 6
  | _ => false

def callableLocalNestedShadowComputedInitializationDoWhileAssignmentStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationDoWhileAssignmentStatementFrame

#guard callableLocalNestedShadowComputedInitializationDoWhileAssignmentStatementFrameWitness

private def localNestedShadowComputedInitializationDoWhileSingleAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.doWhile loopBody condition)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 6
  | _ => false

def callableLocalNestedShadowComputedInitializationDoWhileSingleAssignmentStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationDoWhileSingleAssignmentStatementFrame

#guard callableLocalNestedShadowComputedInitializationDoWhileSingleAssignmentStatementFrameWitness

private def localNestedShadowComputedInitializationDoWhileReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.doWhile loopBody condition)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationDoWhileReturnStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationDoWhileReturnStatementFrame

#guard callableLocalNestedShadowComputedInitializationDoWhileReturnStatementFrameWitness

private def localNestedShadowComputedInitializationDoWhileContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.doWhile loopBody condition)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationDoWhileContinueStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationDoWhileContinueStatementFrame

#guard callableLocalNestedShadowComputedInitializationDoWhileContinueStatementFrameWitness

private def localNestedShadowComputedInitializationDoWhileBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.doWhile loopBody condition)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationDoWhileBreakStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationDoWhileBreakStatementFrame

#guard callableLocalNestedShadowComputedInitializationDoWhileBreakStatementFrameWitness

private def localNestedShadowComputedInitializationForStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let loopBody := .block (.automatic {
    statement := .declare (handle "0x13") intType intType
      (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
    declarations := [handle "0x13"]})
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.forLoop initializer condition step loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationForStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationForStatementFrame

#guard callableLocalNestedShadowComputedInitializationForStatementFrameWitness

private def localNestedShadowComputedInitializationForContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    .continue_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.forLoop initializer condition step loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationForContinueStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationForContinueStatementFrame

#guard callableLocalNestedShadowComputedInitializationForContinueStatementFrameWitness

private def localNestedShadowComputedInitializationForBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.forLoop initializer condition step loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationForBreakStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationForBreakStatementFrame

#guard callableLocalNestedShadowComputedInitializationForBreakStatementFrameWitness

private def localNestedShadowComputedInitializationForReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.forLoop initializer condition step loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationForReturnStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationForReturnStatementFrame

#guard callableLocalNestedShadowComputedInitializationForReturnStatementFrameWitness

private def localNestedShadowComputedInitializationForAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.assign (handle "0x11") {
      expression := .parameter (handle "0x13")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.forLoop initializer condition step loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 6
  | _ => false

def callableLocalNestedShadowComputedInitializationForAssignmentStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationForAssignmentStatementFrame

#guard callableLocalNestedShadowComputedInitializationForAssignmentStatementFrameWitness

private def localNestedShadowComputedInitializationForZeroStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let loopBody := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.assign (handle "0x11") {
      expression := .parameter (handle "0x13")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.forLoop initializer condition step loopBody)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationForZeroStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationForZeroStatementFrame

#guard callableLocalNestedShadowComputedInitializationForZeroStatementFrameWitness

private def localNestedShadowComputedInitializationSwitchStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.switch_ condition [
          {label := some 1, body := .block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            .break_)},
          {label := none, body := .break_}])))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationSwitchStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationSwitchStatementFrame

#guard callableLocalNestedShadowComputedInitializationSwitchStatementFrameWitness

private def localNestedShadowComputedInitializationSwitchAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.switch_ condition [
          {label := some 1, body := .block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.sequence
              (.assign (handle "0x11") {
                expression := .parameter (handle "0x13")
                sourceType := intType
                type := intType})
              .break_))},
          {label := none, body := .break_}])))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 6
  | _ => false

def callableLocalNestedShadowComputedInitializationSwitchAssignmentStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationSwitchAssignmentStatementFrame

#guard callableLocalNestedShadowComputedInitializationSwitchAssignmentStatementFrameWitness

private def localNestedShadowComputedInitializationSwitchAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.switch_ condition [
          {label := some 1, body := .block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.sequence
              (.assign (handle "0x11") {
                expression := .parameter (handle "0x13")
                sourceType := intType
                type := intType})
              .break_))},
          {label := none, body := .break_}])))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationSwitchAssignmentFalseStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationSwitchAssignmentFalseStatementFrame

#guard callableLocalNestedShadowComputedInitializationSwitchAssignmentFalseStatementFrameWitness

private def localNestedShadowComputedInitializationSwitchReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.switch_ condition [
          {label := some 1, body := .block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))},
          {label := none, body := .break_}])))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationSwitchReturnStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationSwitchReturnStatementFrame

#guard callableLocalNestedShadowComputedInitializationSwitchReturnStatementFrameWitness

private def localNestedShadowComputedInitializationSwitchFallthroughStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.switch_ condition [
          {label := some 1, body := .block (.automatic {
            statement := .declare (handle "0x13") intType intType
              (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
            declarations := [handle "0x13"]})},
          {label := none, body := .break_}])))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationSwitchFallthroughStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationSwitchFallthroughStatementFrame

#guard callableLocalNestedShadowComputedInitializationSwitchFallthroughStatementFrameWitness

private def localNestedShadowComputedInitializationConditionalStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.conditional condition
          (.block (.automatic {
            statement := .declare (handle "0x13") intType intType
              (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
            declarations := [handle "0x13"]}))
          .skip)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationConditionalStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationConditionalStatementFrame

#guard callableLocalNestedShadowComputedInitializationConditionalStatementFrameWitness

private def localNestedShadowComputedInitializationConditionalElseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.conditional condition
          .skip
          (.block (.automatic {
            statement := .declare (handle "0x13") intType intType
              (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
            declarations := [handle "0x13"]})))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationConditionalElseStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationConditionalElseStatementFrame

#guard callableLocalNestedShadowComputedInitializationConditionalElseStatementFrameWitness

private def localNestedShadowComputedInitializationConditionalReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.conditional condition
          (.block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType})))
          .skip)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationConditionalReturnStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationConditionalReturnStatementFrame

#guard callableLocalNestedShadowComputedInitializationConditionalReturnStatementFrameWitness

private def localNestedShadowComputedInitializationConditionalElseReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.conditional condition
          .skip
          (.block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationConditionalElseReturnStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationConditionalElseReturnStatementFrame

#guard callableLocalNestedShadowComputedInitializationConditionalElseReturnStatementFrameWitness

private def localNestedShadowComputedInitializationConditionalAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.conditional condition
          (.block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})))
          .skip)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 6
  | _ => false

def callableLocalNestedShadowComputedInitializationConditionalAssignmentStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationConditionalAssignmentStatementFrame

#guard callableLocalNestedShadowComputedInitializationConditionalAssignmentStatementFrameWitness

private def localNestedShadowComputedInitializationConditionalAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.conditional condition
          (.block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})))
          .skip)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationConditionalAssignmentFalseStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationConditionalAssignmentFalseStatementFrame

#guard callableLocalNestedShadowComputedInitializationConditionalAssignmentFalseStatementFrameWitness

private def localNestedShadowComputedInitializationConditionalElseAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.conditional condition
          .skip
          (.block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType}))))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 6
  | _ => false

def callableLocalNestedShadowComputedInitializationConditionalElseAssignmentStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationConditionalElseAssignmentStatementFrame

#guard callableLocalNestedShadowComputedInitializationConditionalElseAssignmentStatementFrameWitness

private def localNestedShadowComputedInitializationConditionalElseAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.conditional condition
          .skip
          (.block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType}))))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationConditionalElseAssignmentFalseStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationConditionalElseAssignmentFalseStatementFrame

#guard callableLocalNestedShadowComputedInitializationConditionalElseAssignmentFalseStatementFrameWitness

private def localNestedShadowComputedInitializationConditionalFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.conditional condition
          (.block (.automatic {
            statement := .declare (handle "0x13") intType intType
              (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
            declarations := [handle "0x13"]}))
          .skip)))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationConditionalFalseStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationConditionalFalseStatementFrame

#guard callableLocalNestedShadowComputedInitializationConditionalFalseStatementFrameWitness

private def localNestedShadowComputedInitializationConditionalElseFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.conditional condition
          .skip
          (.block (.automatic {
            statement := .declare (handle "0x13") intType intType
              (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
            declarations := [handle "0x13"]})))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationConditionalElseFalseStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationConditionalElseFalseStatementFrame

#guard callableLocalNestedShadowComputedInitializationConditionalElseFalseStatementFrameWitness

private def localNestedShadowComputedInitializationSwitchDefaultStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.switch_ condition [
          {label := some 1, body := .break_},
          {label := none, body := .block (.automatic {
            statement := .declare (handle "0x13") intType intType
              (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
            declarations := [handle "0x13"]})}])))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationSwitchDefaultStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationSwitchDefaultStatementFrame

#guard callableLocalNestedShadowComputedInitializationSwitchDefaultStatementFrameWitness

private def localNestedShadowComputedInitializationSwitchDefaultReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.switch_ condition [
          {label := some 1, body := .break_},
          {label := none, body := .block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))}])) )
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationSwitchDefaultReturnStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationSwitchDefaultReturnStatementFrame

#guard callableLocalNestedShadowComputedInitializationSwitchDefaultReturnStatementFrameWitness

private def localNestedShadowComputedInitializationSwitchDefaultAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.switch_ condition [
          {label := some 1, body := .break_},
          {label := none, body := .block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType}))}])) )
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 6
  | _ => false

def callableLocalNestedShadowComputedInitializationSwitchDefaultAssignmentStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationSwitchDefaultAssignmentStatementFrame

#guard callableLocalNestedShadowComputedInitializationSwitchDefaultAssignmentStatementFrameWitness

private def localNestedShadowComputedInitializationSwitchDefaultFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.switch_ condition [
          {label := some 1, body := .block (.automatic {
            statement := .declare (handle "0x13") intType intType
              (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
            declarations := [handle "0x13"]})},
          {label := none, body := .break_}])))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationSwitchDefaultFalseStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationSwitchDefaultFalseStatementFrame

#guard callableLocalNestedShadowComputedInitializationSwitchDefaultFalseStatementFrameWitness

private def localNestedShadowComputedInitializationSwitchDefaultFalseAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.switch_ condition [
          {label := some 1, body := .break_},
          {label := none, body := .block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType}))}])) )
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationSwitchDefaultFalseAssignmentStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationSwitchDefaultFalseAssignmentStatementFrame

#guard callableLocalNestedShadowComputedInitializationSwitchDefaultFalseAssignmentStatementFrameWitness

private def localNestedShadowComputedInitializationSwitchDefaultFalseReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType
            (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
          declarations := [handle "0x12"]})
        (.switch_ condition [
          {label := some 1, body := .block (.sequence
            (.automatic {
              statement := .declare (handle "0x13") intType intType
                (.binary .add (.read (handle "0x12")) (.literal (signed 2)))
              declarations := [handle "0x13"]})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))},
          {label := none, body := .break_}])))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedShadowComputedInitializationSwitchDefaultFalseReturnStatementFrameWitness : Bool :=
  localNestedShadowComputedInitializationSwitchDefaultFalseReturnStatementFrame

#guard callableLocalNestedShadowComputedInitializationSwitchDefaultFalseReturnStatementFrameWitness

private def localNestedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : Expression := .read (handle "0x11")
  let function := {base with body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x11") intType intType (.literal (signed 3))
      declarations := [handle "0x11"]})
    (.sequence
      (.block (.sequence
        (.automatic {
          statement := .declare (handle "0x12") intType intType initializer
          declarations := [handle "0x12"]})
        (.assign (handle "0x10") {
          expression := .parameter (handle "0x12")
          sourceType := intType
          type := intType})))
      (.return_ {
        expression := .parameter (handle "0x10")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 64 .lp64 function [signed 7] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalNestedInitializationStatementFrameWitness : Bool :=
  localNestedInitializationStatementFrame

#guard callableLocalNestedInitializationStatementFrameWitness

private def localConditionalInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (.conditional condition
      (.block (.sequence
        (automaticLiteral "0x11" 5)
        (.assign (handle "0x10") {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))
      .skip)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalConditionalInitializationStatementFrameWitness : Bool :=
  localConditionalInitializationStatementFrame

#guard callableLocalConditionalInitializationStatementFrameWitness

private def localConditionalInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (.conditional condition
      (.block (.sequence
        (automaticLiteral "0x11" 5)
        (.assign (handle "0x10") {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))
      .skip)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableLocalConditionalInitializationFalseStatementFrameWitness : Bool :=
  localConditionalInitializationFalseStatementFrame

#guard callableLocalConditionalInitializationFalseStatementFrameWitness

private def localConditionalElseInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (.conditional condition
      .skip
      (.block (.sequence
        (automaticLiteral "0x11" 5)
        (.assign (handle "0x10") {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))))
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalConditionalElseInitializationStatementFrameWitness : Bool :=
  localConditionalElseInitializationStatementFrame

#guard callableLocalConditionalElseInitializationStatementFrameWitness

private def localConditionalElseInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (.conditional condition
      .skip
      (.block (.sequence
        (automaticLiteral "0x11" 5)
        (.assign (handle "0x10") {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))))
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 1
  | _ => false

def callableLocalConditionalElseInitializationFalseStatementFrameWitness : Bool :=
  localConditionalElseInitializationFalseStatementFrame

#guard callableLocalConditionalElseInitializationFalseStatementFrameWitness

private def localWhileInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (.whileLoop condition body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableLocalWhileInitializationStatementFrameWitness : Bool :=
  localWhileInitializationStatementFrame

#guard callableLocalWhileInitializationStatementFrameWitness

private def localWhileZeroInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (.whileLoop condition body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 1
  | _ => false

def callableLocalWhileZeroInitializationStatementFrameWitness : Bool :=
  localWhileZeroInitializationStatementFrame

#guard callableLocalWhileZeroInitializationStatementFrameWitness

private def localWhileInitializationContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.compoundAssign "+=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (.whileLoop condition body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileInitializationContinueStatementFrameWitness : Bool :=
  localWhileInitializationContinueStatementFrame

#guard callableLocalWhileInitializationContinueStatementFrameWitness

private def localWhileComputedInitializationContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.sequence
        (.compoundAssign "+=" (handle "0x10") {
          expression := .integer 1
          sourceType := intType
          type := intType})
        (.continue_))))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileComputedInitializationContinueStatementFrameWitness : Bool :=
  localWhileComputedInitializationContinueStatementFrame

#guard callableLocalWhileComputedInitializationContinueStatementFrameWitness

private def localWhileComputedInitializationContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.sequence
        (.compoundAssign "+=" (handle "0x10") {
          expression := .integer 1
          sourceType := intType
          type := intType})
        (.continue_))))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileComputedInitializationContinueFalseStatementFrameWitness : Bool :=
  localWhileComputedInitializationContinueFalseStatementFrame

#guard callableLocalWhileComputedInitializationContinueFalseStatementFrameWitness

private def localWhileComputedInitializationBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.break_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalWhileComputedInitializationBreakStatementFrameWitness : Bool :=
  localWhileComputedInitializationBreakStatementFrame

#guard callableLocalWhileComputedInitializationBreakStatementFrameWitness

private def localWhileComputedInitializationBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileComputedInitializationBreakFalseStatementFrameWitness : Bool :=
  localWhileComputedInitializationBreakFalseStatementFrame

#guard callableLocalWhileComputedInitializationBreakFalseStatementFrameWitness

private def localWhileComputedInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalWhileComputedInitializationReturnStatementFrameWitness : Bool :=
  localWhileComputedInitializationReturnStatementFrame

#guard callableLocalWhileComputedInitializationReturnStatementFrameWitness

private def localWhileComputedInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileComputedInitializationReturnFalseStatementFrameWitness : Bool :=
  localWhileComputedInitializationReturnFalseStatementFrame

#guard callableLocalWhileComputedInitializationReturnFalseStatementFrameWitness

private def localWhileInitializationBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.compoundAssign "+=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (.whileLoop condition body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 1
  | _ => false

def callableLocalWhileInitializationBreakStatementFrameWitness : Bool :=
  localWhileInitializationBreakStatementFrame

#guard callableLocalWhileInitializationBreakStatementFrameWitness

private def localWhileInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileInitializationReturnStatementFrameWitness : Bool :=
  localWhileInitializationReturnStatementFrame

#guard callableLocalWhileInitializationReturnStatementFrameWitness

private def localForInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.forLoop initializer condition step (.block (automaticLiteral "0x11" 5)))
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForInitializationStatementFrameWitness : Bool :=
  localForInitializationStatementFrame

#guard callableLocalForInitializationStatementFrameWitness

private def localForZeroInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.forLoop initializer condition step (.block (automaticLiteral "0x11" 5)))
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableLocalForZeroInitializationStatementFrameWitness : Bool :=
  localForZeroInitializationStatementFrame

#guard callableLocalForZeroInitializationStatementFrameWitness

private def localForInitializationContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    .continue_)
  let function := {base with body := .block (.sequence
    (.forLoop initializer condition step body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForInitializationContinueStatementFrameWitness : Bool :=
  localForInitializationContinueStatementFrame

#guard callableLocalForInitializationContinueStatementFrameWitness

private def localForComputedInitializationContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.continue_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForComputedInitializationContinueStatementFrameWitness : Bool :=
  localForComputedInitializationContinueStatementFrame

#guard callableLocalForComputedInitializationContinueStatementFrameWitness

private def localForComputedInitializationContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.continue_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForComputedInitializationContinueFalseStatementFrameWitness : Bool :=
  localForComputedInitializationContinueFalseStatementFrame

#guard callableLocalForComputedInitializationContinueFalseStatementFrameWitness

private def localForComputedInitializationBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.break_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalForComputedInitializationBreakStatementFrameWitness : Bool :=
  localForComputedInitializationBreakStatementFrame

#guard callableLocalForComputedInitializationBreakStatementFrameWitness

private def localForComputedInitializationBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.break_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForComputedInitializationBreakFalseStatementFrameWitness : Bool :=
  localForComputedInitializationBreakFalseStatementFrame

#guard callableLocalForComputedInitializationBreakFalseStatementFrameWitness

private def localForInitializationBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    .break_)
  let function := {base with body := .block (.sequence
    (.forLoop initializer condition step body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableLocalForInitializationBreakStatementFrameWitness : Bool :=
  localForInitializationBreakStatementFrame

#guard callableLocalForInitializationBreakStatementFrameWitness

private def localForInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForInitializationReturnStatementFrameWitness : Bool :=
  localForInitializationReturnStatementFrame

#guard callableLocalForInitializationReturnStatementFrameWitness

private def localDoWhileInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (.doWhile body condition)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableLocalDoWhileInitializationStatementFrameWitness : Bool :=
  localDoWhileInitializationStatementFrame

#guard callableLocalDoWhileInitializationStatementFrameWitness

private def localDoWhileSingleInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (.doWhile body condition)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableLocalDoWhileSingleInitializationStatementFrameWitness : Bool :=
  localDoWhileSingleInitializationStatementFrame

#guard callableLocalDoWhileSingleInitializationStatementFrameWitness

private def localDoWhileInitializationContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.compoundAssign "+=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (.doWhile body condition)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileInitializationContinueStatementFrameWitness : Bool :=
  localDoWhileInitializationContinueStatementFrame

#guard callableLocalDoWhileInitializationContinueStatementFrameWitness

private def localDoWhileComputedInitializationContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.sequence
        (.compoundAssign "+=" (handle "0x10") {
          expression := .integer 1
          sourceType := intType
          type := intType})
        (.continue_))))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileComputedInitializationContinueStatementFrameWitness : Bool :=
  localDoWhileComputedInitializationContinueStatementFrame

#guard callableLocalDoWhileComputedInitializationContinueStatementFrameWitness

private def localDoWhileComputedInitializationContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.sequence
        (.compoundAssign "+=" (handle "0x10") {
          expression := .integer 1
          sourceType := intType
          type := intType})
        (.continue_))))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalDoWhileComputedInitializationContinueFalseStatementFrameWitness : Bool :=
  localDoWhileComputedInitializationContinueFalseStatementFrame

#guard callableLocalDoWhileComputedInitializationContinueFalseStatementFrameWitness

private def localDoWhileComputedInitializationBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.break_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalDoWhileComputedInitializationBreakStatementFrameWitness : Bool :=
  localDoWhileComputedInitializationBreakStatementFrame

#guard callableLocalDoWhileComputedInitializationBreakStatementFrameWitness

private def localDoWhileComputedInitializationBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.break_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalDoWhileComputedInitializationBreakFalseStatementFrameWitness : Bool :=
  localDoWhileComputedInitializationBreakFalseStatementFrame

#guard callableLocalDoWhileComputedInitializationBreakFalseStatementFrameWitness

private def localDoWhileComputedInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalDoWhileComputedInitializationReturnStatementFrameWitness : Bool :=
  localDoWhileComputedInitializationReturnStatementFrame

#guard callableLocalDoWhileComputedInitializationReturnStatementFrameWitness

private def localDoWhileComputedInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalDoWhileComputedInitializationReturnFalseStatementFrameWitness : Bool :=
  localDoWhileComputedInitializationReturnFalseStatementFrame

#guard callableLocalDoWhileComputedInitializationReturnFalseStatementFrameWitness

private def localDoWhileInitializationBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.compoundAssign "+=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (.doWhile body condition)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 1
  | _ => false

def callableLocalDoWhileInitializationBreakStatementFrameWitness : Bool :=
  localDoWhileInitializationBreakStatementFrame

#guard callableLocalDoWhileInitializationBreakStatementFrameWitness

private def localDoWhileInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))}
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileInitializationReturnStatementFrameWitness : Bool :=
  localDoWhileInitializationReturnStatementFrame

#guard callableLocalDoWhileInitializationReturnStatementFrameWitness

private def localDoWhileComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType localInitializer
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "+=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileComputedInitializationStatementFrameWitness : Bool :=
  localDoWhileComputedInitializationStatementFrame

#guard callableLocalDoWhileComputedInitializationStatementFrameWitness

private def localDoWhileComputedInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType localInitializer
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "+=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalDoWhileComputedInitializationFalseStatementFrameWitness : Bool :=
  localDoWhileComputedInitializationFalseStatementFrame

#guard callableLocalDoWhileComputedInitializationFalseStatementFrameWitness

private def localDoWhileSingleComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalDoWhileSingleComputedInitializationStatementFrameWitness : Bool :=
  localDoWhileSingleComputedInitializationStatementFrame

#guard callableLocalDoWhileSingleComputedInitializationStatementFrameWitness

private def localForShadowInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (automaticLiteral "0x13" 5)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowInitializationStatementFrameWitness : Bool :=
  localForShadowInitializationStatementFrame

#guard callableLocalForShadowInitializationStatementFrameWitness

private def localForShadowInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForShadowInitializationAssignmentStatementFrameWitness : Bool :=
  localForShadowInitializationAssignmentStatementFrame

#guard callableLocalForShadowInitializationAssignmentStatementFrameWitness

private def localForShadowInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForShadowInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localForShadowInitializationAssignmentReturnStatementFrame

#guard callableLocalForShadowInitializationAssignmentReturnStatementFrameWitness

private def localForShadowInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForShadowInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localForShadowInitializationAssignmentContinueStatementFrame

#guard callableLocalForShadowInitializationAssignmentContinueStatementFrameWitness

private def localForShadowComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.automatic {
    statement := .declare (handle "0x13") intType intType
      (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
    declarations := [handle "0x13"]})
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationStatementFrameWitness : Bool :=
  localForShadowComputedInitializationStatementFrame

#guard callableLocalForShadowComputedInitializationStatementFrameWitness

private def localForShadowComputedInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.automatic {
    statement := .declare (handle "0x13") intType intType
      (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
    declarations := [handle "0x13"]})
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationFalseStatementFrameWitness : Bool :=
  localForShadowComputedInitializationFalseStatementFrame

#guard callableLocalForShadowComputedInitializationFalseStatementFrameWitness

private def localForShadowComputedInitializationContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.continue_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationContinueFalseStatementFrameWitness : Bool :=
  localForShadowComputedInitializationContinueFalseStatementFrame

#guard callableLocalForShadowComputedInitializationContinueFalseStatementFrameWitness

private def localForShadowComputedInitializationContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    .continue_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationContinueStatementFrameWitness : Bool :=
  localForShadowComputedInitializationContinueStatementFrame

#guard callableLocalForShadowComputedInitializationContinueStatementFrameWitness

private def localForShadowComputedInitializationBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationBreakStatementFrameWitness : Bool :=
  localForShadowComputedInitializationBreakStatementFrame

#guard callableLocalForShadowComputedInitializationBreakStatementFrameWitness

private def localForShadowComputedInitializationBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationBreakFalseStatementFrameWitness : Bool :=
  localForShadowComputedInitializationBreakFalseStatementFrame

#guard callableLocalForShadowComputedInitializationBreakFalseStatementFrameWitness

private def localForShadowComputedInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationReturnStatementFrameWitness : Bool :=
  localForShadowComputedInitializationReturnStatementFrame

#guard callableLocalForShadowComputedInitializationReturnStatementFrameWitness

private def localForShadowComputedInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationReturnFalseStatementFrameWitness : Bool :=
  localForShadowComputedInitializationReturnFalseStatementFrame

#guard callableLocalForShadowComputedInitializationReturnFalseStatementFrameWitness

private def localForShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.assign (handle "0x11") {
      expression := .parameter (handle "0x13")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableLocalForShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localForShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalForShadowComputedInitializationAssignmentStatementFrameWitness

private def localForShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.assign (handle "0x11") {
      expression := .parameter (handle "0x13")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localForShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalForShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localForShadowComputedInitializationSingleAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.assign (handle "0x11") {
      expression := .parameter (handle "0x13")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForShadowComputedInitializationSingleAssignmentStatementFrameWitness : Bool :=
  localForShadowComputedInitializationSingleAssignmentStatementFrame

#guard callableLocalForShadowComputedInitializationSingleAssignmentStatementFrameWitness

private def localForShadowComputedInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableLocalForShadowComputedInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localForShadowComputedInitializationAssignmentContinueStatementFrame

#guard callableLocalForShadowComputedInitializationAssignmentContinueStatementFrameWitness

private def localForShadowComputedInitializationAssignmentContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness : Bool :=
  localForShadowComputedInitializationAssignmentContinueFalseStatementFrame

#guard callableLocalForShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness

private def localForShadowComputedInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForShadowComputedInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localForShadowComputedInitializationAssignmentBreakStatementFrame

#guard callableLocalForShadowComputedInitializationAssignmentBreakStatementFrameWitness

private def localForShadowComputedInitializationAssignmentBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness : Bool :=
  localForShadowComputedInitializationAssignmentBreakFalseStatementFrame

#guard callableLocalForShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness

private def localForShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localForShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalForShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localForShadowComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localForShadowComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalForShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localForShadowComputedInitializationZeroStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.assign (handle "0x11") {
      expression := .parameter (handle "0x13")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForShadowComputedInitializationZeroStatementFrameWitness : Bool :=
  localForShadowComputedInitializationZeroStatementFrame

#guard callableLocalForShadowComputedInitializationZeroStatementFrameWitness

private def localWhileShadowInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileShadowInitializationStatementFrameWitness : Bool :=
  localWhileShadowInitializationStatementFrame

#guard callableLocalWhileShadowInitializationStatementFrameWitness

private def localWhileShadowInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileShadowInitializationAssignmentStatementFrameWitness : Bool :=
  localWhileShadowInitializationAssignmentStatementFrame

#guard callableLocalWhileShadowInitializationAssignmentStatementFrameWitness

private def localWhileShadowInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileShadowInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localWhileShadowInitializationAssignmentReturnStatementFrame

#guard callableLocalWhileShadowInitializationAssignmentReturnStatementFrameWitness

private def localWhileShadowInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.sequence
        (.compoundAssign "-=" (handle "0x10") {
          expression := .integer 1
          sourceType := intType
          type := intType})
        .continue_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileShadowInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localWhileShadowInitializationAssignmentContinueStatementFrame

#guard callableLocalWhileShadowInitializationAssignmentContinueStatementFrameWitness

private def localWhileShadowComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileShadowComputedInitializationStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationStatementFrame

#guard callableLocalWhileShadowComputedInitializationStatementFrameWitness

private def localWhileShadowComputedInitializationContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileShadowComputedInitializationContinueStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationContinueStatementFrame

#guard callableLocalWhileShadowComputedInitializationContinueStatementFrameWitness

private def localWhileShadowComputedInitializationBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileShadowComputedInitializationBreakStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationBreakStatementFrame

#guard callableLocalWhileShadowComputedInitializationBreakStatementFrameWitness

private def localWhileShadowComputedInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileShadowComputedInitializationReturnStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationReturnStatementFrame

#guard callableLocalWhileShadowComputedInitializationReturnStatementFrameWitness

private def localWhileShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableLocalWhileShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalWhileShadowComputedInitializationAssignmentStatementFrameWitness

private def localWhileShadowComputedInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.sequence
        (.compoundAssign "-=" (handle "0x10") {
          expression := .integer 1
          sourceType := intType
          type := intType})
        .continue_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableLocalWhileShadowComputedInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationAssignmentContinueStatementFrame

#guard callableLocalWhileShadowComputedInitializationAssignmentContinueStatementFrameWitness

private def localWhileShadowComputedInitializationAssignmentContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.sequence
        (.compoundAssign "-=" (handle "0x10") {
          expression := .integer 1
          sourceType := intType
          type := intType})
        .continue_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationAssignmentContinueFalseStatementFrame

#guard callableLocalWhileShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness

private def localWhileShadowComputedInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileShadowComputedInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationAssignmentBreakStatementFrame

#guard callableLocalWhileShadowComputedInitializationAssignmentBreakStatementFrameWitness

private def localWhileShadowComputedInitializationAssignmentBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationAssignmentBreakFalseStatementFrame

#guard callableLocalWhileShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness

private def localWhileShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalWhileShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localWhileShadowComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalWhileShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localWhileShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalWhileShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localWhileShadowComputedInitializationSingleAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileShadowComputedInitializationSingleAssignmentStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationSingleAssignmentStatementFrame

#guard callableLocalWhileShadowComputedInitializationSingleAssignmentStatementFrameWitness

private def localWhileShadowComputedInitializationSingleAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileShadowComputedInitializationSingleAssignmentFalseStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationSingleAssignmentFalseStatementFrame

#guard callableLocalWhileShadowComputedInitializationSingleAssignmentFalseStatementFrameWitness

private def localWhileShadowComputedInitializationZeroStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileShadowComputedInitializationZeroStatementFrameWitness : Bool :=
  localWhileShadowComputedInitializationZeroStatementFrame

#guard callableLocalWhileShadowComputedInitializationZeroStatementFrameWitness

private def localDoWhileShadowInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileShadowInitializationStatementFrameWitness : Bool :=
  localDoWhileShadowInitializationStatementFrame

#guard callableLocalDoWhileShadowInitializationStatementFrameWitness

private def localDoWhileShadowInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileShadowInitializationAssignmentStatementFrameWitness : Bool :=
  localDoWhileShadowInitializationAssignmentStatementFrame

#guard callableLocalDoWhileShadowInitializationAssignmentStatementFrameWitness

private def localDoWhileShadowInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileShadowInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localDoWhileShadowInitializationAssignmentReturnStatementFrame

#guard callableLocalDoWhileShadowInitializationAssignmentReturnStatementFrameWitness

private def localDoWhileShadowInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x13" 5)
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.sequence
        (.compoundAssign "-=" (handle "0x10") {
          expression := .integer 1
          sourceType := intType
          type := intType})
        .continue_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileShadowInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localDoWhileShadowInitializationAssignmentContinueStatementFrame

#guard callableLocalDoWhileShadowInitializationAssignmentContinueStatementFrameWitness

private def localDoWhileShadowComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.compoundAssign "-=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileShadowComputedInitializationStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationStatementFrameWitness

private def localDoWhileShadowComputedInitializationContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileShadowComputedInitializationContinueStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationContinueStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationContinueStatementFrameWitness

private def localDoWhileShadowComputedInitializationBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileShadowComputedInitializationBreakStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationBreakStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationBreakStatementFrameWitness

private def localDoWhileShadowComputedInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.return_ {
      expression := .parameter (handle "0x11")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileShadowComputedInitializationReturnStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationReturnStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationReturnStatementFrameWitness

private def localDoWhileShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableLocalDoWhileShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationAssignmentStatementFrameWitness

private def localDoWhileShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localDoWhileShadowComputedInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.sequence
        (.compoundAssign "-=" (handle "0x10") {
          expression := .integer 1
          sourceType := intType
          type := intType})
        .continue_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 7
  | _ => false

def callableLocalDoWhileShadowComputedInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationAssignmentContinueStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationAssignmentContinueStatementFrameWitness

private def localDoWhileShadowComputedInitializationAssignmentContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.sequence
        (.compoundAssign "-=" (handle "0x10") {
          expression := .integer 1
          sourceType := intType
          type := intType})
        .continue_)))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationAssignmentContinueFalseStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness

private def localDoWhileShadowComputedInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileShadowComputedInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationAssignmentBreakStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationAssignmentBreakStatementFrameWitness

private def localDoWhileShadowComputedInitializationAssignmentBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationAssignmentBreakFalseStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness

private def localDoWhileShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localDoWhileShadowComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localDoWhileShadowComputedInitializationSingleAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileShadowComputedInitializationSingleAssignmentStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationSingleAssignmentStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationSingleAssignmentStatementFrameWitness

private def localDoWhileShadowComputedInitializationSingleAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "-=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileShadowComputedInitializationSingleAssignmentFalseStatementFrameWitness : Bool :=
  localDoWhileShadowComputedInitializationSingleAssignmentFalseStatementFrame

#guard callableLocalDoWhileShadowComputedInitializationSingleAssignmentFalseStatementFrameWitness

private def localSwitchShadowInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          .break_)},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowInitializationStatementFrameWitness : Bool :=
  localSwitchShadowInitializationStatementFrame

#guard callableLocalSwitchShadowInitializationStatementFrameWitness

private def localSwitchShadowInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          .break_)},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowInitializationFalseStatementFrameWitness : Bool :=
  localSwitchShadowInitializationFalseStatementFrame

#guard callableLocalSwitchShadowInitializationFalseStatementFrameWitness

private def localSwitchShadowInitializationFallthroughStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (automaticLiteral "0x13" 5)},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowInitializationFallthroughStatementFrameWitness : Bool :=
  localSwitchShadowInitializationFallthroughStatementFrame

#guard callableLocalSwitchShadowInitializationFallthroughStatementFrameWitness

private def localSwitchShadowInitializationFallthroughFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.automatic {
          statement := .declare (handle "0x13") intType intType (.literal (signed 5))
          declarations := [handle "0x13"]})},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowInitializationFallthroughFalseStatementFrameWitness : Bool :=
  localSwitchShadowInitializationFallthroughFalseStatementFrame

#guard callableLocalSwitchShadowInitializationFallthroughFalseStatementFrameWitness

private def localSwitchShadowInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchShadowInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localSwitchShadowInitializationFallthroughAssignmentStatementFrame

#guard callableLocalSwitchShadowInitializationFallthroughAssignmentStatementFrameWitness

private def localSwitchShadowInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchShadowInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchShadowInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalSwitchShadowInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness

private def localSwitchShadowInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localSwitchShadowInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalSwitchShadowInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localSwitchDefaultShadowInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          .break_)}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowInitializationStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationStatementFrameWitness

private def localSwitchDefaultShadowInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          .break_)}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowInitializationFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationFalseStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationFalseStatementFrameWitness

private def localSwitchDefaultShadowInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            .break_))}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultShadowInitializationAssignmentStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationAssignmentStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationAssignmentStatementFrameWitness

private def localSwitchShadowInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            .break_))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchShadowInitializationAssignmentStatementFrameWitness : Bool :=
  localSwitchShadowInitializationAssignmentStatementFrame

#guard callableLocalSwitchShadowInitializationAssignmentStatementFrameWitness

private def localSwitchShadowInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType})))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchShadowInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchShadowInitializationAssignmentReturnStatementFrame

#guard callableLocalSwitchShadowInitializationAssignmentReturnStatementFrameWitness

private def localSwitchShadowInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType})))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchShadowInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchShadowInitializationAssignmentReturnFalseStatementFrameWitness

private def localSwitchShadowInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            .break_))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localSwitchShadowInitializationAssignmentFalseStatementFrame

#guard callableLocalSwitchShadowInitializationAssignmentFalseStatementFrameWitness

private def localForSwitchShadowInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .break_))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchShadowInitializationAssignmentStatementFrameWitness : Bool :=
  localForSwitchShadowInitializationAssignmentStatementFrame

#guard callableLocalForSwitchShadowInitializationAssignmentStatementFrameWitness

private def localForSwitchShadowInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .continue_))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchShadowInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localForSwitchShadowInitializationAssignmentContinueStatementFrame

#guard callableLocalForSwitchShadowInitializationAssignmentContinueStatementFrameWitness

private def localForSwitchShadowInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .break_))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchShadowInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localForSwitchShadowInitializationAssignmentBreakStatementFrame

#guard callableLocalForSwitchShadowInitializationAssignmentBreakStatementFrameWitness

private def localForSwitchShadowInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchShadowInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localForSwitchShadowInitializationAssignmentReturnStatementFrame

#guard callableLocalForSwitchShadowInitializationAssignmentReturnStatementFrameWitness

private def localForSwitchShadowInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .break_))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForSwitchShadowInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localForSwitchShadowInitializationAssignmentFalseStatementFrame

#guard callableLocalForSwitchShadowInitializationAssignmentFalseStatementFrameWitness

private def localForSwitchShadowInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType}))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchShadowInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localForSwitchShadowInitializationFallthroughAssignmentStatementFrame

#guard callableLocalForSwitchShadowInitializationFallthroughAssignmentStatementFrameWitness

private def localForSwitchShadowInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType}))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForSwitchShadowInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localForSwitchShadowInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalForSwitchShadowInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localForSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := none, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType}))},
    {label := some 1, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrame

#guard callableLocalForSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrameWitness

private def localForSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := none, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType}))},
    {label := some 1, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalForSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localForSwitchDefaultShadowInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .break_))}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchDefaultShadowInitializationAssignmentStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowInitializationAssignmentStatementFrame

#guard callableLocalForSwitchDefaultShadowInitializationAssignmentStatementFrameWitness

private def localForSwitchDefaultShadowInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchDefaultShadowInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowInitializationAssignmentReturnStatementFrame

#guard callableLocalForSwitchDefaultShadowInitializationAssignmentReturnStatementFrameWitness

private def localForSwitchDefaultShadowInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .break_))}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForSwitchDefaultShadowInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowInitializationAssignmentFalseStatementFrame

#guard callableLocalForSwitchDefaultShadowInitializationAssignmentFalseStatementFrameWitness

private def localForSwitchDefaultShadowInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .continue_))}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchDefaultShadowInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowInitializationAssignmentContinueStatementFrame

#guard callableLocalForSwitchDefaultShadowInitializationAssignmentContinueStatementFrameWitness

private def localForSwitchDefaultShadowInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchDefaultShadowInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowInitializationAssignmentBreakStatementFrame

#guard callableLocalForSwitchDefaultShadowInitializationAssignmentBreakStatementFrameWitness

private def localForSwitchDefaultShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .break_)) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchDefaultShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalForSwitchDefaultShadowComputedInitializationAssignmentStatementFrameWitness

private def localForSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalForSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localForSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .break_)) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalForSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localForSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := none, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType}))},
    {label := some 1, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrame

#guard callableLocalForSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrameWitness

private def localForSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := none, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType}))},
    {label := some 1, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalForSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localForSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.continue_))) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrame

#guard callableLocalForSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrameWitness

private def localForSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localForSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrame

#guard callableLocalForSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrameWitness

private def localForSwitchShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .break_))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localForSwitchShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalForSwitchShadowComputedInitializationAssignmentStatementFrameWitness

private def localForSwitchShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localForSwitchShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalForSwitchShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localForSwitchShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .break_))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForSwitchShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localForSwitchShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalForSwitchShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localForSwitchShadowComputedInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType}))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchShadowComputedInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localForSwitchShadowComputedInitializationFallthroughAssignmentStatementFrame

#guard callableLocalForSwitchShadowComputedInitializationFallthroughAssignmentStatementFrameWitness

private def localForSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 1
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType}))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localForSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalForSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localForSwitchShadowComputedInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .continue_))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchShadowComputedInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localForSwitchShadowComputedInitializationAssignmentContinueStatementFrame

#guard callableLocalForSwitchShadowComputedInitializationAssignmentContinueStatementFrameWitness

private def localForSwitchShadowComputedInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        .break_))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForSwitchShadowComputedInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localForSwitchShadowComputedInitializationAssignmentBreakStatementFrame

#guard callableLocalForSwitchShadowComputedInitializationAssignmentBreakStatementFrameWitness

private def localWhileSwitchShadowInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowInitializationAssignmentStatementFrameWitness : Bool :=
  localWhileSwitchShadowInitializationAssignmentStatementFrame

#guard callableLocalWhileSwitchShadowInitializationAssignmentStatementFrameWitness

private def localWhileSwitchShadowInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_)))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localWhileSwitchShadowInitializationAssignmentContinueStatementFrame

#guard callableLocalWhileSwitchShadowInitializationAssignmentContinueStatementFrameWitness

private def localWhileSwitchShadowInitializationAssignmentContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_)))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchShadowInitializationAssignmentContinueFalseStatementFrameWitness : Bool :=
  localWhileSwitchShadowInitializationAssignmentContinueFalseStatementFrame

#guard callableLocalWhileSwitchShadowInitializationAssignmentContinueFalseStatementFrameWitness

private def localWhileSwitchShadowInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localWhileSwitchShadowInitializationAssignmentReturnStatementFrame

#guard callableLocalWhileSwitchShadowInitializationAssignmentReturnStatementFrameWitness

private def localWhileSwitchShadowInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchShadowInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localWhileSwitchShadowInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalWhileSwitchShadowInitializationAssignmentReturnFalseStatementFrameWitness

private def localWhileSwitchShadowInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localWhileSwitchShadowInitializationAssignmentBreakStatementFrame

#guard callableLocalWhileSwitchShadowInitializationAssignmentBreakStatementFrameWitness

private def localWhileSwitchShadowInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchShadowInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localWhileSwitchShadowInitializationAssignmentFalseStatementFrame

#guard callableLocalWhileSwitchShadowInitializationAssignmentFalseStatementFrameWitness

private def localWhileSwitchShadowInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localWhileSwitchShadowInitializationFallthroughAssignmentStatementFrame

#guard callableLocalWhileSwitchShadowInitializationFallthroughAssignmentStatementFrameWitness

private def localWhileSwitchShadowInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchShadowInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localWhileSwitchShadowInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalWhileSwitchShadowInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localWhileSwitchShadowInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localWhileSwitchShadowInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalWhileSwitchShadowInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localWhileSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness : Bool :=
  localWhileSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrame

#guard callableLocalWhileSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness
private def localWhileSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrameWitness

private def localWhileSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness
private def localWhileSwitchDefaultShadowInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationAssignmentStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationAssignmentStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationAssignmentStatementFrameWitness

private def localWhileSwitchDefaultShadowInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationAssignmentReturnStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationAssignmentReturnStatementFrameWitness

private def localWhileSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrameWitness

private def localWhileSwitchDefaultShadowInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationAssignmentFalseStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationAssignmentFalseStatementFrameWitness

private def localWhileSwitchDefaultShadowInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_))) }])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationAssignmentContinueStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationAssignmentContinueStatementFrameWitness

private def localWhileSwitchDefaultShadowInitializationAssignmentContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_))) }])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationAssignmentContinueFalseStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationAssignmentContinueFalseStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationAssignmentContinueFalseStatementFrameWitness

private def localWhileSwitchDefaultShadowInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationAssignmentBreakStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationAssignmentBreakStatementFrameWitness

private def localWhileSwitchDefaultShadowInitializationAssignmentBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchDefaultShadowInitializationAssignmentBreakFalseStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowInitializationAssignmentBreakFalseStatementFrame

#guard callableLocalWhileSwitchDefaultShadowInitializationAssignmentBreakFalseStatementFrameWitness

private def localWhileSwitchDefaultShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentStatementFrameWitness

private def localWhileSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localWhileSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localWhileSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrame

#guard callableLocalWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrameWitness

private def localWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localWhileSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_))) }])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrame

#guard callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrameWitness

private def localWhileSwitchDefaultShadowComputedInitializationAssignmentContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_))) }])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowComputedInitializationAssignmentContinueFalseStatementFrame

#guard callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness

private def localWhileSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrame

#guard callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrameWitness

private def localWhileSwitchDefaultShadowComputedInitializationAssignmentBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness : Bool :=
  localWhileSwitchDefaultShadowComputedInitializationAssignmentBreakFalseStatementFrame

#guard callableLocalWhileSwitchDefaultShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationAssignmentStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationFallthroughAssignmentStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationFallthroughAssignmentStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_)))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationAssignmentContinueStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationAssignmentContinueStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationAssignmentContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_)))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationAssignmentContinueFalseStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationAssignmentBreakStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationAssignmentBreakStatementFrameWitness

private def localWhileSwitchShadowComputedInitializationAssignmentBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileSwitchShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness : Bool :=
  localWhileSwitchShadowComputedInitializationAssignmentBreakFalseStatementFrame

#guard callableLocalWhileSwitchShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness

private def localDoWhileSwitchShadowInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowInitializationAssignmentStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowInitializationAssignmentStatementFrame

#guard callableLocalDoWhileSwitchShadowInitializationAssignmentStatementFrameWitness

private def localDoWhileSwitchShadowInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_)))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowInitializationAssignmentContinueStatementFrame

#guard callableLocalDoWhileSwitchShadowInitializationAssignmentContinueStatementFrameWitness

private def localDoWhileSwitchShadowInitializationAssignmentContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_)))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchShadowInitializationAssignmentContinueFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowInitializationAssignmentContinueFalseStatementFrame

#guard callableLocalDoWhileSwitchShadowInitializationAssignmentContinueFalseStatementFrameWitness

private def localDoWhileSwitchShadowInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowInitializationAssignmentReturnStatementFrame

#guard callableLocalDoWhileSwitchShadowInitializationAssignmentReturnStatementFrameWitness

private def localDoWhileSwitchShadowInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowInitializationAssignmentBreakStatementFrame

#guard callableLocalDoWhileSwitchShadowInitializationAssignmentBreakStatementFrameWitness

private def localDoWhileSwitchShadowInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchShadowInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalDoWhileSwitchShadowInitializationAssignmentReturnFalseStatementFrameWitness

private def localDoWhileSwitchShadowInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchShadowInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowInitializationAssignmentFalseStatementFrame

#guard callableLocalDoWhileSwitchShadowInitializationAssignmentFalseStatementFrameWitness

private def localDoWhileSwitchDefaultShadowInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationAssignmentStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentStatementFrameWitness

private def localDoWhileSwitchDefaultShadowInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType}))) }])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationAssignmentReturnStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentReturnStatementFrameWitness

private def localDoWhileSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (automaticLiteral "0x13" 5)
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrameWitness

private def localDoWhileSwitchDefaultShadowInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationAssignmentFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentFalseStatementFrameWitness

private def localDoWhileSwitchDefaultShadowInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_))) }])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationAssignmentContinueStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentContinueStatementFrameWitness

private def localDoWhileSwitchDefaultShadowInitializationAssignmentContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_))) }])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentContinueFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationAssignmentContinueFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentContinueFalseStatementFrameWitness

private def localDoWhileSwitchDefaultShadowInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationAssignmentBreakStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentBreakStatementFrameWitness

private def localDoWhileSwitchDefaultShadowInitializationAssignmentBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentBreakFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationAssignmentBreakFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationAssignmentBreakFalseStatementFrameWitness
private def localDoWhileSwitchDefaultShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .break_},
    {label := none, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))) }])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalsePathStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalsePathStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalsePathStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalsePathStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_))) }])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentContinueStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationAssignmentContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_))) }])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationAssignmentContinueFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentBreakStatementFrameWitness

private def localDoWhileSwitchDefaultShadowComputedInitializationAssignmentBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .break_},
      {label := none, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowComputedInitializationAssignmentBreakFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationAssignmentStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.switch_ switchCondition [
    {label := some 0, body := .block (.sequence
      (.automatic {
        statement := .declare (handle "0x13") intType intType localInitializer
        declarations := [handle "0x13"]})
      (.sequence
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType})
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType})))},
    {label := none, body := .break_}])
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_)))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationAssignmentContinueStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationAssignmentContinueStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationAssignmentContinueFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          (.sequence
            (.compoundAssign "+=" (handle "0x10") {
              expression := .integer 1
              sourceType := intType
              type := intType})
            .continue_)))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationAssignmentContinueFalseStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationAssignmentContinueFalseStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationAssignmentBreakStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationAssignmentBreakStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationAssignmentBreakFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.sequence
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    .break_)
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationAssignmentBreakFalseStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationAssignmentBreakFalseStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationFallthroughAssignmentStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationFallthroughAssignmentStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localDoWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrame

#guard callableLocalDoWhileSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrameWitness

private def localDoWhileSwitchShadowInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowInitializationFallthroughAssignmentStatementFrame

#guard callableLocalDoWhileSwitchShadowInitializationFallthroughAssignmentStatementFrameWitness

private def localDoWhileSwitchShadowInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchShadowInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalDoWhileSwitchShadowInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localDoWhileSwitchShadowInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchShadowInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalDoWhileSwitchShadowInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localDoWhileSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := some 0, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrame

#guard callableLocalDoWhileSwitchShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness
private def localDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrameWitness

private def localDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let switchCondition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.switch_ switchCondition [
      {label := none, body := .block (.sequence
        (automaticLiteral "0x13" 5)
        (.assign (handle "0x11") {
          expression := .parameter (handle "0x13")
          sourceType := intType
          type := intType}))},
      {label := some 1, body := .break_}])
    (.compoundAssign "+=" (handle "0x10") {
      expression := .integer 1
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.doWhile body condition)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness : Bool :=
  localDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrame

#guard callableLocalDoWhileSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness
private def localSwitchShadowInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowInitializationReturnStatementFrameWitness : Bool :=
  localSwitchShadowInitializationReturnStatementFrame

#guard callableLocalSwitchShadowInitializationReturnStatementFrameWitness

private def localSwitchShadowInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowInitializationReturnFalseStatementFrameWitness : Bool :=
  localSwitchShadowInitializationReturnFalseStatementFrame

#guard callableLocalSwitchShadowInitializationReturnFalseStatementFrameWitness

private def localSwitchDefaultShadowInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType}))}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowInitializationReturnStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationReturnStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationReturnStatementFrameWitness

private def localSwitchDefaultShadowInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType}))}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowInitializationReturnFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationReturnFalseStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationReturnFalseStatementFrameWitness

private def localSwitchDefaultShadowInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))) }])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultShadowInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationAssignmentReturnStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationAssignmentReturnStatementFrameWitness

private def localSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))) }])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationAssignmentReturnFalseStatementFrameWitness

private def localSwitchDefaultShadowInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            .break_))}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationAssignmentFalseStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationAssignmentFalseStatementFrameWitness

private def localSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := some 1, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationFallthroughAssignmentStatementFrameWitness

private def localSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            .break_))},
        {label := some 1, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := some 1, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := none, body := .block (.sequence
          (automaticLiteral "0x13" 5)
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := some 1, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchDefaultShadowInitializationFallthroughAssignmentReturnFalseStatementFrameWitness

private def localSwitchShadowComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          .break_)},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowComputedInitializationStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationStatementFrame

#guard callableLocalSwitchShadowComputedInitializationStatementFrameWitness

private def localSwitchShadowComputedInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          .break_)},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowComputedInitializationFalseStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationFalseStatementFrame

#guard callableLocalSwitchShadowComputedInitializationFalseStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          .break_) }])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.break_))}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationFalseStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationFalseStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            .break_)) }])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationAssignmentStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))) }])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))) }])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            .break_)) }])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := some 1, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationFallthroughAssignmentStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := some 1, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := some 1, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := some 1, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})) }])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationReturnStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationReturnStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationReturnStatementFrameWitness

private def localSwitchDefaultShadowComputedInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})) }])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultShadowComputedInitializationReturnFalseStatementFrameWitness : Bool :=
  localSwitchDefaultShadowComputedInitializationReturnFalseStatementFrame

#guard callableLocalSwitchDefaultShadowComputedInitializationReturnFalseStatementFrameWitness

private def localSwitchShadowComputedInitializationFallthroughStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowComputedInitializationFallthroughStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationFallthroughStatementFrame

#guard callableLocalSwitchShadowComputedInitializationFallthroughStatementFrameWitness

private def localSwitchShadowComputedInitializationFallthroughFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowComputedInitializationFallthroughFalseStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationFallthroughFalseStatementFrame

#guard callableLocalSwitchShadowComputedInitializationFallthroughFalseStatementFrameWitness

private def localSwitchShadowComputedInitializationFallthroughAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchShadowComputedInitializationFallthroughAssignmentStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationFallthroughAssignmentStatementFrame

#guard callableLocalSwitchShadowComputedInitializationFallthroughAssignmentStatementFrameWitness

private def localSwitchShadowComputedInitializationFallthroughAssignmentDirectFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowComputedInitializationFallthroughAssignmentDirectFalseStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationFallthroughAssignmentDirectFalseStatementFrame

#guard callableLocalSwitchShadowComputedInitializationFallthroughAssignmentDirectFalseStatementFrameWitness

private def localSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 0, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrame

#guard callableLocalSwitchShadowComputedInitializationFallthroughAssignmentFalseStatementFrameWitness

private def localSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrame

#guard callableLocalSwitchShadowComputedInitializationFallthroughAssignmentReturnStatementFrameWitness

private def localSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchShadowComputedInitializationFallthroughAssignmentReturnFalseStatementFrameWitness

private def localSwitchShadowComputedInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowComputedInitializationReturnStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationReturnStatementFrame

#guard callableLocalSwitchShadowComputedInitializationReturnStatementFrameWitness

private def localSwitchShadowComputedInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowComputedInitializationReturnFalseStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationReturnFalseStatementFrame

#guard callableLocalSwitchShadowComputedInitializationReturnFalseStatementFrameWitness

private def localSwitchShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            .break_))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalSwitchShadowComputedInitializationAssignmentStatementFrameWitness

private def localSwitchShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType})))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalSwitchShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType})))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localSwitchShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            .break_))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localSwitchShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalSwitchShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localConditionalShadowInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        (.block (automaticLiteral "0x13" 5))
        .skip)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalShadowInitializationStatementFrameWitness : Bool :=
  localConditionalShadowInitializationStatementFrame

#guard callableLocalConditionalShadowInitializationStatementFrameWitness

private def localConditionalShadowComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        (.block (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]}))
        .skip)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalShadowComputedInitializationStatementFrameWitness : Bool :=
  localConditionalShadowComputedInitializationStatementFrame

#guard callableLocalConditionalShadowComputedInitializationStatementFrameWitness

private def localConditionalElseShadowComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        .skip
        (.block (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalElseShadowComputedInitializationStatementFrameWitness : Bool :=
  localConditionalElseShadowComputedInitializationStatementFrame

#guard callableLocalConditionalElseShadowComputedInitializationStatementFrameWitness

private def localConditionalShadowComputedInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType
              (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
            declarations := [handle "0x13"]})
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})))
        .skip)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalShadowComputedInitializationReturnStatementFrameWitness : Bool :=
  localConditionalShadowComputedInitializationReturnStatementFrame

#guard callableLocalConditionalShadowComputedInitializationReturnStatementFrameWitness

private def localConditionalShadowComputedInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType
              (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
            declarations := [handle "0x13"]})
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})))
        .skip)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalShadowComputedInitializationReturnFalseStatementFrameWitness : Bool :=
  localConditionalShadowComputedInitializationReturnFalseStatementFrame

#guard callableLocalConditionalShadowComputedInitializationReturnFalseStatementFrameWitness

private def localConditionalElseShadowComputedInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        .skip
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType
              (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
            declarations := [handle "0x13"]})
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType}))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalElseShadowComputedInitializationReturnStatementFrameWitness : Bool :=
  localConditionalElseShadowComputedInitializationReturnStatementFrame

#guard callableLocalConditionalElseShadowComputedInitializationReturnStatementFrameWitness

private def localConditionalElseShadowComputedInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        .skip
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType
              (.binary .add (.read (handle "0x11")) (.literal (signed 2)))
            declarations := [handle "0x13"]})
          (.return_ {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType}))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalElseShadowComputedInitializationReturnFalseStatementFrameWitness : Bool :=
  localConditionalElseShadowComputedInitializationReturnFalseStatementFrame

#guard callableLocalConditionalElseShadowComputedInitializationReturnFalseStatementFrameWitness

private def localConditionalShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})))
        .skip)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalConditionalShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localConditionalShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalConditionalShadowComputedInitializationAssignmentStatementFrameWitness

private def localConditionalShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))))
        .skip)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalConditionalShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localConditionalShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalConditionalShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localConditionalElseShadowComputedInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        .skip
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalConditionalElseShadowComputedInitializationAssignmentStatementFrameWitness : Bool :=
  localConditionalElseShadowComputedInitializationAssignmentStatementFrame

#guard callableLocalConditionalElseShadowComputedInitializationAssignmentStatementFrameWitness

private def localConditionalElseShadowComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        .skip
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType})))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalConditionalElseShadowComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localConditionalElseShadowComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalConditionalElseShadowComputedInitializationAssignmentReturnStatementFrameWitness

private def localConditionalElseShadowComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        .skip
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType})))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalElseShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localConditionalElseShadowComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalConditionalElseShadowComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localConditionalShadowComputedInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        (.block (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]}))
        .skip)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalShadowComputedInitializationFalseStatementFrameWitness : Bool :=
  localConditionalShadowComputedInitializationFalseStatementFrame

#guard callableLocalConditionalShadowComputedInitializationFalseStatementFrameWitness

private def localConditionalElseShadowComputedInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        .skip
        (.block (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]})))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalElseShadowComputedInitializationFalseStatementFrameWitness : Bool :=
  localConditionalElseShadowComputedInitializationFalseStatementFrame

#guard callableLocalConditionalElseShadowComputedInitializationFalseStatementFrameWitness

private def localConditionalShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})))
        .skip)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localConditionalShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalConditionalShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localConditionalElseShadowComputedInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        .skip
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalElseShadowComputedInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localConditionalElseShadowComputedInitializationAssignmentFalseStatementFrame

#guard callableLocalConditionalElseShadowComputedInitializationAssignmentFalseStatementFrameWitness

private def localConditionalComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType})))
        .skip)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalConditionalComputedInitializationStatementFrameWitness : Bool :=
  localConditionalComputedInitializationStatementFrame

#guard callableLocalConditionalComputedInitializationStatementFrameWitness

private def localConditionalComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))))
        .skip)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalConditionalComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localConditionalComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalConditionalComputedInitializationAssignmentReturnStatementFrameWitness

private def localConditionalFalseComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        (.block (.automatic {
          statement := .declare (handle "0x13") intType intType localInitializer
          declarations := [handle "0x13"]}))
        .skip)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalFalseComputedInitializationStatementFrameWitness : Bool :=
  localConditionalFalseComputedInitializationStatementFrame

#guard callableLocalConditionalFalseComputedInitializationStatementFrameWitness

private def localConditionalElseComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        .skip
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalConditionalElseComputedInitializationStatementFrameWitness : Bool :=
  localConditionalElseComputedInitializationStatementFrame

#guard callableLocalConditionalElseComputedInitializationStatementFrameWitness

private def localConditionalElseComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        .skip
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType})))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalConditionalElseComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localConditionalElseComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalConditionalElseComputedInitializationAssignmentReturnStatementFrameWitness

private def localConditionalElseComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.conditional condition
        .skip
        (.block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType})))))
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalConditionalElseComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localConditionalElseComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalConditionalElseComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localForComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType localInitializer
      declarations := [handle "0x13"]})
    (.assign (handle "0x11") {
      expression := .parameter (handle "0x13")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForComputedInitializationStatementFrameWitness : Bool :=
  localForComputedInitializationStatementFrame

#guard callableLocalForComputedInitializationStatementFrameWitness

private def localForComputedInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType localInitializer
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalForComputedInitializationReturnStatementFrameWitness : Bool :=
  localForComputedInitializationReturnStatementFrame

#guard callableLocalForComputedInitializationReturnStatementFrameWitness

private def localForComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType localInitializer
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 4
  | _ => false

def callableLocalForComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localForComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalForComputedInitializationAssignmentReturnStatementFrameWitness

private def localForComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType localInitializer
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localForComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalForComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localForComputedInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType localInitializer
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForComputedInitializationReturnFalseStatementFrameWitness : Bool :=
  localForComputedInitializationReturnFalseStatementFrame

#guard callableLocalForComputedInitializationReturnFalseStatementFrameWitness

private def localForZeroComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 2
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.assign (handle "0x11") {
      expression := .parameter (handle "0x13")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.forLoop initializer condition step body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalForZeroComputedInitializationStatementFrameWitness : Bool :=
  localForZeroComputedInitializationStatementFrame

#guard callableLocalForZeroComputedInitializationStatementFrameWitness

private def localSwitchComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchComputedInitializationStatementFrameWitness : Bool :=
  localSwitchComputedInitializationStatementFrame

#guard callableLocalSwitchComputedInitializationStatementFrameWitness

private def localSwitchComputedInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.assign (handle "0x11") {
            expression := .parameter (handle "0x13")
            sourceType := intType
            type := intType}))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchComputedInitializationFalseStatementFrameWitness : Bool :=
  localSwitchComputedInitializationFalseStatementFrame

#guard callableLocalSwitchComputedInitializationFalseStatementFrameWitness

private def localSwitchComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType})))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalSwitchComputedInitializationAssignmentReturnStatementFrameWitness

private def localSwitchComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType})))},
        {label := none, body := .break_}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localSwitchDefaultComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.break_)))}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultComputedInitializationStatementFrameWitness : Bool :=
  localSwitchDefaultComputedInitializationStatementFrame

#guard callableLocalSwitchDefaultComputedInitializationStatementFrameWitness

private def localSwitchDefaultComputedInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.break_)))}])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultComputedInitializationFalseStatementFrameWitness : Bool :=
  localSwitchDefaultComputedInitializationFalseStatementFrame

#guard callableLocalSwitchDefaultComputedInitializationFalseStatementFrameWitness

private def localSwitchDefaultComputedInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))) }])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultComputedInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchDefaultComputedInitializationAssignmentReturnStatementFrame

#guard callableLocalSwitchDefaultComputedInitializationAssignmentReturnStatementFrameWitness

private def localSwitchDefaultComputedInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 2))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.switch_ condition [
        {label := some 1, body := .break_},
        {label := none, body := .block (.sequence
          (.automatic {
            statement := .declare (handle "0x13") intType intType localInitializer
            declarations := [handle "0x13"]})
          (.sequence
            (.assign (handle "0x11") {
              expression := .parameter (handle "0x13")
              sourceType := intType
              type := intType})
            (.return_ {
              expression := .parameter (handle "0x11")
              sourceType := intType
              type := intType}))) }])
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalSwitchDefaultComputedInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchDefaultComputedInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchDefaultComputedInitializationAssignmentReturnFalseStatementFrameWitness

private def localSwitchInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.assign (handle "0x10") {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchInitializationStatementFrameWitness : Bool :=
  localSwitchInitializationStatementFrame

#guard callableLocalSwitchInitializationStatementFrameWitness

private def localSwitchInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.assign (handle "0x10") {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableLocalSwitchInitializationFalseStatementFrameWitness : Bool :=
  localSwitchInitializationFalseStatementFrame

#guard callableLocalSwitchInitializationFalseStatementFrameWitness

private def localSwitchInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchInitializationReturnStatementFrameWitness : Bool :=
  localSwitchInitializationReturnStatementFrame

#guard callableLocalSwitchInitializationReturnStatementFrameWitness

private def localSwitchInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))},
      {label := none, body := .break_}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableLocalSwitchInitializationReturnFalseStatementFrameWitness : Bool :=
  localSwitchInitializationReturnFalseStatementFrame

#guard callableLocalSwitchInitializationReturnFalseStatementFrameWitness

private def localSwitchDefaultInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.sequence
          (.assign (handle "0x10") {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})
          .break_))}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultInitializationStatementFrameWitness : Bool :=
  localSwitchDefaultInitializationStatementFrame

#guard callableLocalSwitchDefaultInitializationStatementFrameWitness

private def localSwitchDefaultInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.break_))}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 1
  | _ => false

def callableLocalSwitchDefaultInitializationFalseStatementFrameWitness : Bool :=
  localSwitchDefaultInitializationFalseStatementFrame

#guard callableLocalSwitchDefaultInitializationFalseStatementFrameWitness

private def localSwitchDefaultInitializationReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultInitializationReturnStatementFrameWitness : Bool :=
  localSwitchDefaultInitializationReturnStatementFrame

#guard callableLocalSwitchDefaultInitializationReturnStatementFrameWitness

private def localSwitchDefaultInitializationReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.return_ {
          expression := .parameter (handle "0x11")
          sourceType := intType
          type := intType}))}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 1
  | _ => false

def callableLocalSwitchDefaultInitializationReturnFalseStatementFrameWitness : Bool :=
  localSwitchDefaultInitializationReturnFalseStatementFrame

#guard callableLocalSwitchDefaultInitializationReturnFalseStatementFrameWitness

private def localSwitchInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.sequence
          (.assign (handle "0x10") {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchInitializationAssignmentStatementFrameWitness : Bool :=
  localSwitchInitializationAssignmentStatementFrame

#guard callableLocalSwitchInitializationAssignmentStatementFrameWitness

private def localSwitchInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.sequence
          (.assign (handle "0x10") {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})
          .break_))},
      {label := none, body := .break_}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableLocalSwitchInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localSwitchInitializationAssignmentFalseStatementFrame

#guard callableLocalSwitchInitializationAssignmentFalseStatementFrameWitness

private def localSwitchDefaultInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.sequence
          (.assign (handle "0x10") {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})
          .break_))}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultInitializationAssignmentStatementFrameWitness : Bool :=
  localSwitchDefaultInitializationAssignmentStatementFrame

#guard callableLocalSwitchDefaultInitializationAssignmentStatementFrameWitness

private def localSwitchDefaultInitializationAssignmentFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.sequence
          (.assign (handle "0x10") {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})
          .break_))}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 1
  | _ => false

def callableLocalSwitchDefaultInitializationAssignmentFalseStatementFrameWitness : Bool :=
  localSwitchDefaultInitializationAssignmentFalseStatementFrame

#guard callableLocalSwitchDefaultInitializationAssignmentFalseStatementFrameWitness

private def localSwitchInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.sequence
          (.assign (handle "0x10") {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})
          (.return_ {
            expression := .parameter (handle "0x10")
            sourceType := intType
            type := intType})))},
      {label := none, body := .break_}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchInitializationAssignmentReturnStatementFrame

#guard callableLocalSwitchInitializationAssignmentReturnStatementFrameWitness

private def localSwitchInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.sequence
          (.assign (handle "0x10") {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})
          (.return_ {
            expression := .parameter (handle "0x10")
            sourceType := intType
            type := intType})))},
      {label := none, body := .break_}])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 0
  | _ => false

def callableLocalSwitchInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchInitializationAssignmentReturnFalseStatementFrameWitness

private def localSwitchDefaultInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.sequence
          (.assign (handle "0x10") {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})
          (.return_ {
            expression := .parameter (handle "0x10")
            sourceType := intType
            type := intType}))) }])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalSwitchDefaultInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localSwitchDefaultInitializationAssignmentReturnStatementFrame

#guard callableLocalSwitchDefaultInitializationAssignmentReturnStatementFrameWitness

private def localSwitchDefaultInitializationAssignmentReturnFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .parameter (handle "0x10")
    sourceType := intType
    type := intType}
  let function := {base with body := .block (.sequence
    (.switch_ condition [
      {label := some 1, body := .break_},
      {label := none, body := .block (.sequence
        (automaticLiteral "0x11" 5)
        (.sequence
          (.assign (handle "0x10") {
            expression := .parameter (handle "0x11")
            sourceType := intType
            type := intType})
          (.return_ {
            expression := .parameter (handle "0x10")
            sourceType := intType
            type := intType}))) }])
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 1
  | _ => false

def callableLocalSwitchDefaultInitializationAssignmentReturnFalseStatementFrameWitness : Bool :=
  localSwitchDefaultInitializationAssignmentReturnFalseStatementFrame

#guard callableLocalSwitchDefaultInitializationAssignmentReturnFalseStatementFrameWitness

private def localWhileInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.assign (handle "0x10") {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (.whileLoop condition body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileInitializationAssignmentStatementFrameWitness : Bool :=
  localWhileInitializationAssignmentStatementFrame

#guard callableLocalWhileInitializationAssignmentStatementFrameWitness

private def localWhileInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.assign (handle "0x10") {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x10")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (.whileLoop condition body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localWhileInitializationAssignmentReturnStatementFrame

#guard callableLocalWhileInitializationAssignmentReturnStatementFrameWitness

private def localWhileInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.assign (handle "0x10") {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (.whileLoop condition body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localWhileInitializationAssignmentContinueStatementFrame

#guard callableLocalWhileInitializationAssignmentContinueStatementFrameWitness

private def localDoWhileInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.assign (handle "0x10") {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (.doWhile body condition)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileInitializationAssignmentStatementFrameWitness : Bool :=
  localDoWhileInitializationAssignmentStatementFrame

#guard callableLocalDoWhileInitializationAssignmentStatementFrameWitness

private def localDoWhileInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 0, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.assign (handle "0x10") {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x10")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (.doWhile body condition)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localDoWhileInitializationAssignmentReturnStatementFrame

#guard callableLocalDoWhileInitializationAssignmentReturnStatementFrameWitness

private def localDoWhileInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.assign (handle "0x10") {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (.doWhile body condition)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 64 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalDoWhileInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localDoWhileInitializationAssignmentContinueStatementFrame

#guard callableLocalDoWhileInitializationAssignmentContinueStatementFrameWitness

private def localForInitializationAssignmentStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.assign (handle "0x10") {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (.forLoop initializer condition step body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForInitializationAssignmentStatementFrameWitness : Bool :=
  localForInitializationAssignmentStatementFrame

#guard callableLocalForInitializationAssignmentStatementFrameWitness

private def localForInitializationAssignmentReturnStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.assign (handle "0x10") {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})
      (.return_ {
        expression := .parameter (handle "0x10")
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (.forLoop initializer condition step body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForInitializationAssignmentReturnStatementFrameWitness : Bool :=
  localForInitializationAssignmentReturnStatementFrame

#guard callableLocalForInitializationAssignmentReturnStatementFrameWitness

private def localForInitializationAssignmentContinueStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.assign (handle "0x10") {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})
      .continue_))
  let function := {base with body := .block (.sequence
    (.forLoop initializer condition step body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 6
  | _ => false

def callableLocalForInitializationAssignmentContinueStatementFrameWitness : Bool :=
  localForInitializationAssignmentContinueStatementFrame

#guard callableLocalForInitializationAssignmentContinueStatementFrameWitness

private def localForInitializationAssignmentBreakStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let initializer : CallableStatement := .assign (handle "0x10") {
    expression := .integer 0
    sourceType := intType
    type := intType}
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 3, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let step : CallableStatement := .expression {
    expression := .increment "++" false (handle "0x10")
    sourceType := intType
    type := intType}
  let body := .block (.sequence
    (automaticLiteral "0x11" 5)
    (.sequence
      (.assign (handle "0x10") {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType})
      .break_))
  let function := {base with body := .block (.sequence
    (.forLoop initializer condition step body)
    (.return_ {
      expression := .parameter (handle "0x10")
      sourceType := intType
      type := intType}))}
  match evaluateCallableObject 128 .lp64 function [signed 9] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalForInitializationAssignmentBreakStatementFrameWitness : Bool :=
  localForInitializationAssignmentBreakStatementFrame

#guard callableLocalForInitializationAssignmentBreakStatementFrameWitness

private def localWhileComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType localInitializer
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "+=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 0] with
  | .ok (.ok value) => value == signed 5
  | _ => false

def callableLocalWhileComputedInitializationStatementFrameWitness : Bool :=
  localWhileComputedInitializationStatementFrame

#guard callableLocalWhileComputedInitializationStatementFrameWitness

private def localWhileComputedInitializationFalseStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary "<"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 2, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let localInitializer : Expression :=
    .binary .add (.read (handle "0x11")) (.literal (signed 1))
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType localInitializer
      declarations := [handle "0x13"]})
    (.sequence
      (.assign (handle "0x11") {
        expression := .parameter (handle "0x13")
        sourceType := intType
        type := intType})
      (.compoundAssign "+=" (handle "0x10") {
        expression := .integer 1
        sourceType := intType
        type := intType})))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 2] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileComputedInitializationFalseStatementFrameWitness : Bool :=
  localWhileComputedInitializationFalseStatementFrame

#guard callableLocalWhileComputedInitializationFalseStatementFrameWitness

private def localWhileZeroComputedInitializationStatementFrame : Bool :=
  let base := incrementFunction .int "++" false
  let condition : TypedCallableExpression := {
    expression := .binary ">"
      {expression := .parameter (handle "0x10"), sourceType := intType, type := intType}
      {expression := .integer 1, sourceType := intType, type := intType}
    sourceType := intType
    type := .builtin .boolean}
  let body := .block (.sequence
    (.automatic {
      statement := .declare (handle "0x13") intType intType
        (.binary .add (.read (handle "0x11")) (.literal (signed 1)))
      declarations := [handle "0x13"]})
    (.assign (handle "0x11") {
      expression := .parameter (handle "0x13")
      sourceType := intType
      type := intType}))
  let function := {base with body := .block (.sequence
    (automaticLiteral "0x11" 3)
    (.sequence
      (.whileLoop condition body)
      (.return_ {
        expression := .parameter (handle "0x11")
        sourceType := intType
        type := intType}))) }
  match evaluateCallableObject 128 .lp64 function [signed 1] with
  | .ok (.ok value) => value == signed 3
  | _ => false

def callableLocalWhileZeroComputedInitializationStatementFrameWitness : Bool :=
  localWhileZeroComputedInitializationStatementFrame

#guard callableLocalWhileZeroComputedInitializationStatementFrameWitness

private def checkIncrement (type : CppIntType) (operator : String) (isPostfix : Bool)
    (argument expected : IntegralValue) : Bool :=
  let function := incrementFunction type operator isPostfix
  (evaluateCallableObject 16 .lp64 function [argument]).toOption == some (.ok expected) &&
    (evaluateCallable 16 .lp64 function [argument]).toOption == some (.ok expected)

def callableShortFrameIncrementWitness : Bool :=
  checkIncrement .short "++" false ⟨.signed 16, 32767⟩ ⟨.signed 16, -32768⟩

#guard checkIncrement .short "++" false ⟨.signed 16, 32767⟩ ⟨.signed 16, -32768⟩
#guard callableShortFrameIncrementWitness

def callableShortFrameIncrementMidWitness : Bool :=
  checkIncrement .short "++" false ⟨.signed 16, 12⟩ ⟨.signed 16, 13⟩

#guard callableShortFrameIncrementMidWitness

def callableShortFrameDecrementMidWitness : Bool :=
  checkIncrement .short "--" false ⟨.signed 16, 12⟩ ⟨.signed 16, 11⟩

#guard callableShortFrameDecrementMidWitness

def callableShortFrameDecrementWitness : Bool :=
  checkIncrement .short "--" false ⟨.signed 16, -32768⟩ ⟨.signed 16, 32767⟩

#guard callableShortFrameDecrementWitness

def callableShortPostfixReturnWitness : Bool :=
  checkIncrement .short "++" true ⟨.signed 16, 32766⟩ ⟨.signed 16, 32766⟩

#guard callableShortPostfixReturnWitness

def callableUnsignedShortPostfixReturnWitness : Bool :=
  checkIncrement .unsignedShort "++" true ⟨.unsigned 16, 65535⟩ ⟨.unsigned 16, 65535⟩

#guard callableUnsignedShortPostfixReturnWitness

def callableUnsignedShortFrameIncrementWitness : Bool :=
  checkIncrement .unsignedShort "++" false ⟨.unsigned 16, 65535⟩ ⟨.unsigned 16, 0⟩

#guard callableUnsignedShortFrameIncrementWitness

def callableUnsignedShortPostfixIncrementMidWitness : Bool :=
  checkIncrement .unsignedShort "++" true ⟨.unsigned 16, 12⟩ ⟨.unsigned 16, 12⟩

#guard callableUnsignedShortPostfixIncrementMidWitness

def callableSignedCharFrameIncrementWitness : Bool :=
  checkIncrement .signedChar "++" false ⟨.signed 8, 127⟩ ⟨.signed 8, -128⟩

#guard callableSignedCharFrameIncrementWitness

def callableSignedCharFrameDecrementWitness : Bool :=
  checkIncrement .signedChar "--" false ⟨.signed 8, -128⟩ ⟨.signed 8, 127⟩

#guard callableSignedCharFrameDecrementWitness

def callableSignedCharPostfixReturnWitness : Bool :=
  checkIncrement .signedChar "++" true ⟨.signed 8, 126⟩ ⟨.signed 8, 126⟩

#guard callableSignedCharPostfixReturnWitness

def callableUnsignedCharFrameIncrementWitness : Bool :=
  checkIncrement .unsignedChar "++" false ⟨.unsigned 8, 255⟩ ⟨.unsigned 8, 0⟩

#guard callableUnsignedCharFrameIncrementWitness

def callableUnsignedCharFrameDecrementWitness : Bool :=
  checkIncrement .unsignedChar "--" false ⟨.unsigned 8, 0⟩ ⟨.unsigned 8, 255⟩

#guard callableUnsignedCharFrameDecrementWitness

def callableUnsignedCharPostfixReturnWitness : Bool :=
  checkIncrement .unsignedChar "++" true ⟨.unsigned 8, 255⟩ ⟨.unsigned 8, 255⟩

#guard callableUnsignedCharPostfixReturnWitness

def callableSignedCharPostfixDecrementWitness : Bool :=
  checkIncrement .signedChar "--" true ⟨.signed 8, -127⟩ ⟨.signed 8, -127⟩

#guard callableSignedCharPostfixDecrementWitness

def callableUnsignedCharPostfixDecrementWitness : Bool :=
  checkIncrement .unsignedChar "--" true ⟨.unsigned 8, 0⟩ ⟨.unsigned 8, 0⟩

#guard callableUnsignedCharPostfixDecrementWitness

def callableShortPostfixDecrementWitness : Bool :=
  checkIncrement .short "--" true ⟨.signed 16, -32767⟩ ⟨.signed 16, -32767⟩

#guard callableShortPostfixDecrementWitness

def callableUnsignedShortPostfixDecrementWitness : Bool :=
  checkIncrement .unsignedShort "--" true ⟨.unsigned 16, 0⟩ ⟨.unsigned 16, 0⟩

#guard callableUnsignedShortPostfixDecrementWitness

private def unsignedShortFrameDecrement : Bool :=
  match CallableObjectFrame.start .lp64 (incrementFunction .unsignedShort "--" false)
      [⟨.unsigned 16, 0⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 16 started
      match outcome.result with
      | .ok (.ok value) => value == ⟨.unsigned 16, 65535⟩
      | _ => false

def callableUnsignedShortFrameDecrementWitness : Bool := unsignedShortFrameDecrement

#guard callableUnsignedShortFrameDecrementWitness
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

def callablePostfixStoreWitness : Bool := postfixStore

private def unsignedFrameIncrement : Bool :=
  match CallableObjectFrame.start .lp64 (incrementFunction .unsignedInt "++" false)
      [⟨.unsigned 32, 4294967295⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 16 started
      match outcome.result with
      | .ok (.ok value) => value == ⟨.unsigned 32, 0⟩
      | _ => false

def callableUnsignedFrameIncrementWitness : Bool := unsignedFrameIncrement

private def unsignedPostfixStore : Bool :=
  let function := incrementFunction .unsignedInt "++" true
  let function := {function with body := match function.body with
    | .return_ expression => .expression expression
    | other => other}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 4294967295⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 16 started
      (outcome.result matches .error .missingReturn) &&
        (outcome.frame.read (handle "0x10")).result.toOption ==
          some ⟨.unsigned 32, 0⟩

def callableUnsignedPostfixStoreWitness : Bool := unsignedPostfixStore

private def unsignedFrameDecrement : Bool :=
  match CallableObjectFrame.start .lp64 (incrementFunction .unsignedInt "--" false)
      [⟨.unsigned 32, 0⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 16 started
      match outcome.result with
      | .ok (.ok value) => value == ⟨.unsigned 32, 4294967295⟩
      | _ => false

def callableUnsignedFrameDecrementWitness : Bool := unsignedFrameDecrement

private def unsignedPostfixDecrementStore : Bool :=
  let function := incrementFunction .unsignedInt "--" true
  let function := {function with body := match function.body with
    | .return_ expression => .expression expression
    | other => other}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 0⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 16 started
      (outcome.result matches .error .missingReturn) &&
        (outcome.frame.read (handle "0x10")).result.toOption ==
          some ⟨.unsigned 32, 4294967295⟩

def callableUnsignedPostfixDecrementStoreWitness : Bool := unsignedPostfixDecrementStore

private def unsignedPostfixReturn : Bool :=
  match evaluateCallableObject 16 .lp64
      (incrementFunction .unsignedInt "++" true) [⟨.unsigned 32, 4294967295⟩] with
  | .ok (.ok value) => value == ⟨.unsigned 32, 4294967295⟩
  | _ => false

def callableUnsignedPostfixReturnWitness : Bool := unsignedPostfixReturn

private def unsignedCompoundFrame : Bool :=
  let base := incrementFunction .unsignedInt "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedInt,
        type := .builtin .unsignedInt})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedInt, type := .builtin .unsignedInt}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 4294967295⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 32, 0⟩)

def callableUnsignedCompoundFrameWitness : Bool := unsignedCompoundFrame

private def unsignedShortCompoundFrame : Bool :=
  let base := incrementFunction .unsignedShort "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedShort,
        type := .builtin .unsignedShort})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedShort, type := .builtin .unsignedShort}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 16, 65535⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 16, 0⟩)

def callableUnsignedShortCompoundFrameWitness : Bool := unsignedShortCompoundFrame

#guard callableUnsignedShortCompoundFrameWitness

private def unsignedShortCompoundAddFrame : Bool :=
  let base := incrementFunction .unsignedShort "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedShort,
        type := .builtin .unsignedShort})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedShort, type := .builtin .unsignedShort}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 16, 15⟩)

def callableUnsignedShortCompoundAddFrameWitness : Bool :=
  unsignedShortCompoundAddFrame

#guard callableUnsignedShortCompoundAddFrameWitness

private def unsignedCharCompoundAddFrame : Bool :=
  let base := incrementFunction .unsignedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedChar,
        type := .builtin .unsignedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedChar, type := .builtin .unsignedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 8, 15⟩)

def callableUnsignedCharCompoundAddFrameWitness : Bool :=
  unsignedCharCompoundAddFrame

#guard callableUnsignedCharCompoundAddFrameWitness

private def signedShortCompoundFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .short,
        type := .builtin .short})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .short, type := .builtin .short}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 16, 13⟩)

def callableShortCompoundFrameWitness : Bool := signedShortCompoundFrame

#guard callableShortCompoundFrameWitness

private def unsignedCharCompoundFrame : Bool :=
  let base := incrementFunction .unsignedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedChar,
        type := .builtin .unsignedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedChar, type := .builtin .unsignedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 8, 255⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 8, 0⟩)

def callableUnsignedCharCompoundFrameWitness : Bool := unsignedCharCompoundFrame

#guard callableUnsignedCharCompoundFrameWitness

private def signedCharCompoundFrame : Bool :=
  let base := incrementFunction .signedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .signedChar,
        type := .builtin .signedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .signedChar, type := .builtin .signedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 8, 13⟩)

def callableSignedCharCompoundFrameWitness : Bool := signedCharCompoundFrame

#guard callableSignedCharCompoundFrameWitness

private def signedCharCompoundSubtractFrame : Bool :=
  let base := incrementFunction .signedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "-=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .signedChar,
        type := .builtin .signedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .signedChar, type := .builtin .signedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 8, 9⟩)

def callableSignedCharCompoundSubtractFrameWitness : Bool :=
  signedCharCompoundSubtractFrame

#guard callableSignedCharCompoundSubtractFrameWitness

private def signedCharCompoundModuloFrame : Bool :=
  let base := incrementFunction .signedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "%=" (handle "0x10")
      {expression := .integer 5, sourceType := .builtin .signedChar,
        type := .builtin .signedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .signedChar, type := .builtin .signedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 8, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 8, 3⟩)

def callableSignedCharCompoundModuloFrameWitness : Bool :=
  signedCharCompoundModuloFrame

#guard callableSignedCharCompoundModuloFrameWitness

private def shortCompoundSubtractFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "-=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .short,
        type := .builtin .short})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .short, type := .builtin .short}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 16, 11⟩)

def callableShortCompoundSubtractFrameWitness : Bool := shortCompoundSubtractFrame

#guard callableShortCompoundSubtractFrameWitness

private def unsignedShortCompoundSubtractFrame : Bool :=
  let base := incrementFunction .unsignedShort "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "-=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedShort,
        type := .builtin .unsignedShort})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedShort, type := .builtin .unsignedShort}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 16, 0⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 16, 65535⟩)

def callableUnsignedShortCompoundSubtractFrameWitness : Bool :=
  unsignedShortCompoundSubtractFrame

#guard callableUnsignedShortCompoundSubtractFrameWitness

private def unsignedCharCompoundSubtractFrame : Bool :=
  let base := incrementFunction .unsignedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "-=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedChar,
        type := .builtin .unsignedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedChar, type := .builtin .unsignedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 8, 0⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 8, 255⟩)

def callableUnsignedCharCompoundSubtractFrameWitness : Bool :=
  unsignedCharCompoundSubtractFrame

#guard callableUnsignedCharCompoundSubtractFrameWitness

private def shortCompoundMultiplyFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "*=" (handle "0x10")
      {expression := .integer 4, sourceType := .builtin .short,
        type := .builtin .short})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .short, type := .builtin .short}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 16, 3⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 16, 12⟩)

def callableShortCompoundMultiplyFrameWitness : Bool := shortCompoundMultiplyFrame

#guard callableShortCompoundMultiplyFrameWitness

private def unsignedCharCompoundMultiplyFrame : Bool :=
  let base := incrementFunction .unsignedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "*=" (handle "0x10")
      {expression := .integer 4, sourceType := .builtin .unsignedChar,
        type := .builtin .unsignedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedChar, type := .builtin .unsignedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 8, 3⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 8, 12⟩)

def callableUnsignedCharCompoundMultiplyFrameWitness : Bool :=
  unsignedCharCompoundMultiplyFrame

#guard callableUnsignedCharCompoundMultiplyFrameWitness

private def unsignedShortCompoundMultiplyFrame : Bool :=
  let base := incrementFunction .unsignedShort "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "*=" (handle "0x10")
      {expression := .integer 4, sourceType := .builtin .unsignedShort,
        type := .builtin .unsignedShort})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedShort, type := .builtin .unsignedShort}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 16, 3⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 16, 12⟩)

def callableUnsignedShortCompoundMultiplyFrameWitness : Bool :=
  unsignedShortCompoundMultiplyFrame

#guard callableUnsignedShortCompoundMultiplyFrameWitness

private def signedCharCompoundMultiplyFrame : Bool :=
  let base := incrementFunction .signedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "*=" (handle "0x10")
      {expression := .integer 4, sourceType := .builtin .signedChar,
        type := .builtin .signedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .signedChar, type := .builtin .signedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 8, 3⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 8, 12⟩)

def callableSignedCharCompoundMultiplyFrameWitness : Bool :=
  signedCharCompoundMultiplyFrame

#guard callableSignedCharCompoundMultiplyFrameWitness

private def shortCompoundDivideFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "/=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .short,
        type := .builtin .short})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .short, type := .builtin .short}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 16, 4⟩)

def callableShortCompoundDivideFrameWitness : Bool := shortCompoundDivideFrame

#guard callableShortCompoundDivideFrameWitness

private def shortCompoundModuloFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "%=" (handle "0x10")
      {expression := .integer 5, sourceType := .builtin .short,
        type := .builtin .short})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .short, type := .builtin .short}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 16, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 16, 3⟩)

def callableShortCompoundModuloFrameWitness : Bool := shortCompoundModuloFrame

#guard callableShortCompoundModuloFrameWitness

private def unsignedShortCompoundDivideFrame : Bool :=
  let base := incrementFunction .unsignedShort "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "/=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedShort,
        type := .builtin .unsignedShort})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedShort, type := .builtin .unsignedShort}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 16, 4⟩)

def callableUnsignedShortCompoundDivideFrameWitness : Bool :=
  unsignedShortCompoundDivideFrame

#guard callableUnsignedShortCompoundDivideFrameWitness

private def unsignedShortCompoundModuloFrame : Bool :=
  let base := incrementFunction .unsignedShort "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "%=" (handle "0x10")
      {expression := .integer 5, sourceType := .builtin .unsignedShort,
        type := .builtin .unsignedShort})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedShort, type := .builtin .unsignedShort}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 16, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 16, 3⟩)

def callableUnsignedShortCompoundModuloFrameWitness : Bool :=
  unsignedShortCompoundModuloFrame

#guard callableUnsignedShortCompoundModuloFrameWitness

private def unsignedCharCompoundDivideFrame : Bool :=
  let base := incrementFunction .unsignedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "/=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedChar,
        type := .builtin .unsignedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedChar, type := .builtin .unsignedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 8, 4⟩)

def callableUnsignedCharCompoundDivideFrameWitness : Bool :=
  unsignedCharCompoundDivideFrame

#guard callableUnsignedCharCompoundDivideFrameWitness

private def unsignedCharCompoundModuloFrame : Bool :=
  let base := incrementFunction .unsignedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "%=" (handle "0x10")
      {expression := .integer 5, sourceType := .builtin .unsignedChar,
        type := .builtin .unsignedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedChar, type := .builtin .unsignedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 8, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 8, 3⟩)

def callableUnsignedCharCompoundModuloFrameWitness : Bool :=
  unsignedCharCompoundModuloFrame

#guard callableUnsignedCharCompoundModuloFrameWitness

private def signedCharCompoundDivideFrame : Bool :=
  let base := incrementFunction .signedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "/=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .signedChar,
        type := .builtin .signedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .signedChar, type := .builtin .signedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 8, 4⟩)

def callableSignedCharCompoundDivideFrameWitness : Bool :=
  signedCharCompoundDivideFrame

#guard callableSignedCharCompoundDivideFrameWitness

private def shortCompoundBitAndFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "&=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .short,
        type := .builtin .short})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .short, type := .builtin .short}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 16, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 16, 1⟩)

def callableShortCompoundBitAndFrameWitness : Bool := shortCompoundBitAndFrame

#guard callableShortCompoundBitAndFrameWitness

private def shortCompoundBitOrFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "|=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .short,
        type := .builtin .short})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .short, type := .builtin .short}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 16, 15⟩)

def callableShortCompoundBitOrFrameWitness : Bool := shortCompoundBitOrFrame

#guard callableShortCompoundBitOrFrameWitness

private def shortCompoundBitXorFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "^=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .short,
        type := .builtin .short})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .short, type := .builtin .short}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 16, 15⟩)

def callableShortCompoundBitXorFrameWitness : Bool := shortCompoundBitXorFrame

#guard callableShortCompoundBitXorFrameWitness

private def unsignedShortCompoundBitAndFrame : Bool :=
  let base := incrementFunction .unsignedShort "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "&=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedShort,
        type := .builtin .unsignedShort})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedShort, type := .builtin .unsignedShort}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 16, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 16, 1⟩)

def callableUnsignedShortCompoundBitAndFrameWitness : Bool :=
  unsignedShortCompoundBitAndFrame

#guard callableUnsignedShortCompoundBitAndFrameWitness

private def unsignedShortCompoundBitOrFrame : Bool :=
  let base := incrementFunction .unsignedShort "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "|=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedShort,
        type := .builtin .unsignedShort})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedShort, type := .builtin .unsignedShort}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 16, 15⟩)

def callableUnsignedShortCompoundBitOrFrameWitness : Bool :=
  unsignedShortCompoundBitOrFrame

#guard callableUnsignedShortCompoundBitOrFrameWitness

private def unsignedShortCompoundBitXorFrame : Bool :=
  let base := incrementFunction .unsignedShort "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "^=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedShort,
        type := .builtin .unsignedShort})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedShort, type := .builtin .unsignedShort}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 16, 15⟩)

def callableUnsignedShortCompoundBitXorFrameWitness : Bool :=
  unsignedShortCompoundBitXorFrame

#guard callableUnsignedShortCompoundBitXorFrameWitness

private def signedCharCompoundBitAndFrame : Bool :=
  let base := incrementFunction .signedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "&=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .signedChar,
        type := .builtin .signedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .signedChar, type := .builtin .signedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 8, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 8, 1⟩)

def callableSignedCharCompoundBitAndFrameWitness : Bool :=
  signedCharCompoundBitAndFrame

#guard callableSignedCharCompoundBitAndFrameWitness

private def signedCharCompoundBitOrFrame : Bool :=
  let base := incrementFunction .signedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "|=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .signedChar,
        type := .builtin .signedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .signedChar, type := .builtin .signedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 8, 15⟩)

def callableSignedCharCompoundBitOrFrameWitness : Bool :=
  signedCharCompoundBitOrFrame

#guard callableSignedCharCompoundBitOrFrameWitness

private def signedCharCompoundBitXorFrame : Bool :=
  let base := incrementFunction .signedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "^=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .signedChar,
        type := .builtin .signedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .signedChar, type := .builtin .signedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 8, 15⟩)

def callableSignedCharCompoundBitXorFrameWitness : Bool :=
  signedCharCompoundBitXorFrame

#guard callableSignedCharCompoundBitXorFrameWitness

private def unsignedCharCompoundBitAndFrame : Bool :=
  let base := incrementFunction .unsignedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "&=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedChar,
        type := .builtin .unsignedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedChar, type := .builtin .unsignedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 8, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 8, 1⟩)

def callableUnsignedCharCompoundBitAndFrameWitness : Bool :=
  unsignedCharCompoundBitAndFrame

#guard callableUnsignedCharCompoundBitAndFrameWitness

private def unsignedCharCompoundBitOrFrame : Bool :=
  let base := incrementFunction .unsignedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "|=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedChar,
        type := .builtin .unsignedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedChar, type := .builtin .unsignedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 8, 15⟩)

def callableUnsignedCharCompoundBitOrFrameWitness : Bool :=
  unsignedCharCompoundBitOrFrame

#guard callableUnsignedCharCompoundBitOrFrameWitness

private def unsignedCharCompoundBitXorFrame : Bool :=
  let base := incrementFunction .unsignedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "^=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedChar,
        type := .builtin .unsignedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedChar, type := .builtin .unsignedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 8, 15⟩)

def callableUnsignedCharCompoundBitXorFrameWitness : Bool :=
  unsignedCharCompoundBitXorFrame

#guard callableUnsignedCharCompoundBitXorFrameWitness

private def shortCompoundShiftLeftFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "<<=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .short,
        type := .builtin .short})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .short, type := .builtin .short}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 16, 24⟩)

def callableShortCompoundShiftLeftFrameWitness : Bool :=
  shortCompoundShiftLeftFrame

#guard callableShortCompoundShiftLeftFrameWitness

private def shortCompoundShiftRightFrame : Bool :=
  let base := incrementFunction .short "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign ">>=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .short,
        type := .builtin .short})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .short, type := .builtin .short}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 16, 6⟩)

def callableShortCompoundShiftRightFrameWitness : Bool :=
  shortCompoundShiftRightFrame

#guard callableShortCompoundShiftRightFrameWitness

private def unsignedShortCompoundShiftLeftFrame : Bool :=
  let base := incrementFunction .unsignedShort "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "<<=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedShort,
        type := .builtin .unsignedShort})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedShort, type := .builtin .unsignedShort}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 16, 24⟩)

def callableUnsignedShortCompoundShiftLeftFrameWitness : Bool :=
  unsignedShortCompoundShiftLeftFrame

#guard callableUnsignedShortCompoundShiftLeftFrameWitness

private def unsignedShortCompoundShiftRightFrame : Bool :=
  let base := incrementFunction .unsignedShort "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign ">>=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedShort,
        type := .builtin .unsignedShort})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedShort, type := .builtin .unsignedShort}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 16, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 16, 6⟩)

def callableUnsignedShortCompoundShiftRightFrameWitness : Bool :=
  unsignedShortCompoundShiftRightFrame

#guard callableUnsignedShortCompoundShiftRightFrameWitness

private def signedCharCompoundShiftLeftFrame : Bool :=
  let base := incrementFunction .signedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "<<=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .signedChar,
        type := .builtin .signedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .signedChar, type := .builtin .signedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 8, 24⟩)

def callableSignedCharCompoundShiftLeftFrameWitness : Bool :=
  signedCharCompoundShiftLeftFrame

#guard callableSignedCharCompoundShiftLeftFrameWitness

private def signedCharCompoundShiftRightFrame : Bool :=
  let base := incrementFunction .signedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign ">>=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .signedChar,
        type := .builtin .signedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .signedChar, type := .builtin .signedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 8, 6⟩)

def callableSignedCharCompoundShiftRightFrameWitness : Bool :=
  signedCharCompoundShiftRightFrame

#guard callableSignedCharCompoundShiftRightFrameWitness

private def unsignedCharCompoundShiftLeftFrame : Bool :=
  let base := incrementFunction .unsignedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "<<=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedChar,
        type := .builtin .unsignedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedChar, type := .builtin .unsignedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 8, 24⟩)

def callableUnsignedCharCompoundShiftLeftFrameWitness : Bool :=
  unsignedCharCompoundShiftLeftFrame

#guard callableUnsignedCharCompoundShiftLeftFrameWitness

private def unsignedCharCompoundShiftRightFrame : Bool :=
  let base := incrementFunction .unsignedChar "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign ">>=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedChar,
        type := .builtin .unsignedChar})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedChar, type := .builtin .unsignedChar}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 8, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 8, 6⟩)

def callableUnsignedCharCompoundShiftRightFrameWitness : Bool :=
  unsignedCharCompoundShiftRightFrame

#guard callableUnsignedCharCompoundShiftRightFrameWitness

private def intCompoundShiftLeftFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "<<=" (handle "0x10")
      {expression := .integer 2, sourceType := .builtin .int,
        type := .builtin .int})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .int, type := .builtin .int}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 32, 3⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 32, 12⟩)

def callableIntCompoundShiftLeftFrameWitness : Bool :=
  intCompoundShiftLeftFrame

#guard callableIntCompoundShiftLeftFrameWitness

private def intCompoundShiftRightFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign ">>=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .int,
        type := .builtin .int})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .int, type := .builtin .int}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 32, 6⟩)

def callableIntCompoundShiftRightFrameWitness : Bool :=
  intCompoundShiftRightFrame

#guard callableIntCompoundShiftRightFrameWitness

private def intCompoundAddFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .int,
        type := .builtin .int})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .int, type := .builtin .int}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 32, 15⟩)

def callableIntCompoundAddFrameWitness : Bool :=
  intCompoundAddFrame

#guard callableIntCompoundAddFrameWitness

private def intCompoundSubtractFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "-=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .int,
        type := .builtin .int})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .int, type := .builtin .int}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 32, 9⟩)

def callableIntCompoundSubtractFrameWitness : Bool :=
  intCompoundSubtractFrame

#guard callableIntCompoundSubtractFrameWitness

private def intCompoundMultiplyFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "*=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .int,
        type := .builtin .int})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .int, type := .builtin .int}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 32, 4⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 32, 12⟩)

def callableIntCompoundMultiplyFrameWitness : Bool :=
  intCompoundMultiplyFrame

#guard callableIntCompoundMultiplyFrameWitness

private def intCompoundDivideFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "/=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .int,
        type := .builtin .int})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .int, type := .builtin .int}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 32, 4⟩)

def callableIntCompoundDivideFrameWitness : Bool :=
  intCompoundDivideFrame

#guard callableIntCompoundDivideFrameWitness

private def intCompoundModuloFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "%=" (handle "0x10")
      {expression := .integer 5, sourceType := .builtin .int,
        type := .builtin .int})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .int, type := .builtin .int}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 32, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 32, 3⟩)

def callableIntCompoundModuloFrameWitness : Bool :=
  intCompoundModuloFrame

#guard callableIntCompoundModuloFrameWitness

private def unsignedIntCompoundAddFrame : Bool :=
  let base := incrementFunction .unsignedInt "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedInt,
        type := .builtin .unsignedInt})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedInt, type := .builtin .unsignedInt}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 32, 15⟩)

def callableUnsignedIntCompoundAddFrameWitness : Bool :=
  unsignedIntCompoundAddFrame

#guard callableUnsignedIntCompoundAddFrameWitness

private def unsignedIntCompoundSubtractFrame : Bool :=
  let base := incrementFunction .unsignedInt "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "-=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedInt,
        type := .builtin .unsignedInt})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedInt, type := .builtin .unsignedInt}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 32, 9⟩)

def callableUnsignedIntCompoundSubtractFrameWitness : Bool :=
  unsignedIntCompoundSubtractFrame

#guard callableUnsignedIntCompoundSubtractFrameWitness

private def unsignedIntCompoundMultiplyFrame : Bool :=
  let base := incrementFunction .unsignedInt "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "*=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedInt,
        type := .builtin .unsignedInt})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedInt, type := .builtin .unsignedInt}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 4⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 32, 12⟩)

def callableUnsignedIntCompoundMultiplyFrameWitness : Bool :=
  unsignedIntCompoundMultiplyFrame

#guard callableUnsignedIntCompoundMultiplyFrameWitness

private def unsignedIntCompoundDivideFrame : Bool :=
  let base := incrementFunction .unsignedInt "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "/=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedInt,
        type := .builtin .unsignedInt})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedInt, type := .builtin .unsignedInt}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 32, 4⟩)

def callableUnsignedIntCompoundDivideFrameWitness : Bool :=
  unsignedIntCompoundDivideFrame

#guard callableUnsignedIntCompoundDivideFrameWitness

private def unsignedIntCompoundModuloFrame : Bool :=
  let base := incrementFunction .unsignedInt "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "%=" (handle "0x10")
      {expression := .integer 5, sourceType := .builtin .unsignedInt,
        type := .builtin .unsignedInt})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedInt, type := .builtin .unsignedInt}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 32, 3⟩)

def callableUnsignedIntCompoundModuloFrameWitness : Bool :=
  unsignedIntCompoundModuloFrame

#guard callableUnsignedIntCompoundModuloFrameWitness

private def unsignedIntCompoundBitAndFrame : Bool :=
  let base := incrementFunction .unsignedInt "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "&=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedInt,
        type := .builtin .unsignedInt})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedInt, type := .builtin .unsignedInt}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 32, 1⟩)

def callableUnsignedIntCompoundBitAndFrameWitness : Bool :=
  unsignedIntCompoundBitAndFrame

#guard callableUnsignedIntCompoundBitAndFrameWitness

private def unsignedIntCompoundBitOrFrame : Bool :=
  let base := incrementFunction .unsignedInt "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "|=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedInt,
        type := .builtin .unsignedInt})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedInt, type := .builtin .unsignedInt}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 32, 15⟩)

def callableUnsignedIntCompoundBitOrFrameWitness : Bool :=
  unsignedIntCompoundBitOrFrame

#guard callableUnsignedIntCompoundBitOrFrameWitness

private def unsignedIntCompoundBitXorFrame : Bool :=
  let base := incrementFunction .unsignedInt "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "^=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedInt,
        type := .builtin .unsignedInt})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedInt, type := .builtin .unsignedInt}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 32, 15⟩)

def callableUnsignedIntCompoundBitXorFrameWitness : Bool :=
  unsignedIntCompoundBitXorFrame

#guard callableUnsignedIntCompoundBitXorFrameWitness

private def unsignedIntCompoundShiftLeftFrame : Bool :=
  let base := incrementFunction .unsignedInt "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "<<=" (handle "0x10")
      {expression := .integer 2, sourceType := .builtin .unsignedInt,
        type := .builtin .unsignedInt})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedInt, type := .builtin .unsignedInt}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 3⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 32, 12⟩)

def callableUnsignedIntCompoundShiftLeftFrameWitness : Bool :=
  unsignedIntCompoundShiftLeftFrame

#guard callableUnsignedIntCompoundShiftLeftFrameWitness

private def unsignedIntCompoundShiftRightFrame : Bool :=
  let base := incrementFunction .unsignedInt "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign ">>=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedInt,
        type := .builtin .unsignedInt})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedInt, type := .builtin .unsignedInt}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 32, 6⟩)

def callableUnsignedIntCompoundShiftRightFrameWitness : Bool :=
  unsignedIntCompoundShiftRightFrame

#guard callableUnsignedIntCompoundShiftRightFrameWitness

private def unsignedLongLongCompoundAddFrame : Bool :=
  let base := incrementFunction .unsignedLongLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLongLong,
        type := .builtin .unsignedLongLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLongLong, type := .builtin .unsignedLongLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 15⟩)

def callableUnsignedLongLongCompoundAddFrameWitness : Bool :=
  unsignedLongLongCompoundAddFrame

#guard callableUnsignedLongLongCompoundAddFrameWitness

private def unsignedLongLongCompoundSubtractFrame : Bool :=
  let base := incrementFunction .unsignedLongLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "-=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLongLong,
        type := .builtin .unsignedLongLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLongLong, type := .builtin .unsignedLongLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 9⟩)

def callableUnsignedLongLongCompoundSubtractFrameWitness : Bool :=
  unsignedLongLongCompoundSubtractFrame

#guard callableUnsignedLongLongCompoundSubtractFrameWitness

private def unsignedLongLongCompoundMultiplyFrame : Bool :=
  let base := incrementFunction .unsignedLongLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "*=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLongLong,
        type := .builtin .unsignedLongLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLongLong, type := .builtin .unsignedLongLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 4⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 12⟩)

def callableUnsignedLongLongCompoundMultiplyFrameWitness : Bool :=
  unsignedLongLongCompoundMultiplyFrame

#guard callableUnsignedLongLongCompoundMultiplyFrameWitness

private def unsignedLongLongCompoundDivideFrame : Bool :=
  let base := incrementFunction .unsignedLongLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "/=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLongLong,
        type := .builtin .unsignedLongLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLongLong, type := .builtin .unsignedLongLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 4⟩)

def callableUnsignedLongLongCompoundDivideFrameWitness : Bool :=
  unsignedLongLongCompoundDivideFrame

#guard callableUnsignedLongLongCompoundDivideFrameWitness

private def unsignedLongLongCompoundModuloFrame : Bool :=
  let base := incrementFunction .unsignedLongLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "%=" (handle "0x10")
      {expression := .integer 5, sourceType := .builtin .unsignedLongLong,
        type := .builtin .unsignedLongLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLongLong, type := .builtin .unsignedLongLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 3⟩)

def callableUnsignedLongLongCompoundModuloFrameWitness : Bool :=
  unsignedLongLongCompoundModuloFrame

#guard callableUnsignedLongLongCompoundModuloFrameWitness

private def unsignedLongLongCompoundBitAndFrame : Bool :=
  let base := incrementFunction .unsignedLongLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "&=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLongLong,
        type := .builtin .unsignedLongLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLongLong, type := .builtin .unsignedLongLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 1⟩)

def callableUnsignedLongLongCompoundBitAndFrameWitness : Bool :=
  unsignedLongLongCompoundBitAndFrame

#guard callableUnsignedLongLongCompoundBitAndFrameWitness

private def unsignedLongLongCompoundBitOrFrame : Bool :=
  let base := incrementFunction .unsignedLongLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "|=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLongLong,
        type := .builtin .unsignedLongLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLongLong, type := .builtin .unsignedLongLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 15⟩)

def callableUnsignedLongLongCompoundBitOrFrameWitness : Bool :=
  unsignedLongLongCompoundBitOrFrame

#guard callableUnsignedLongLongCompoundBitOrFrameWitness

private def unsignedLongLongCompoundBitXorFrame : Bool :=
  let base := incrementFunction .unsignedLongLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "^=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLongLong,
        type := .builtin .unsignedLongLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLongLong, type := .builtin .unsignedLongLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 15⟩)

def callableUnsignedLongLongCompoundBitXorFrameWitness : Bool :=
  unsignedLongLongCompoundBitXorFrame

#guard callableUnsignedLongLongCompoundBitXorFrameWitness

private def unsignedLongLongCompoundShiftLeftFrame : Bool :=
  let base := incrementFunction .unsignedLongLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "<<=" (handle "0x10")
      {expression := .integer 2, sourceType := .builtin .unsignedLongLong,
        type := .builtin .unsignedLongLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLongLong, type := .builtin .unsignedLongLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 3⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 12⟩)

def callableUnsignedLongLongCompoundShiftLeftFrameWitness : Bool :=
  unsignedLongLongCompoundShiftLeftFrame

#guard callableUnsignedLongLongCompoundShiftLeftFrameWitness

private def unsignedLongLongCompoundShiftRightFrame : Bool :=
  let base := incrementFunction .unsignedLongLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign ">>=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedLongLong,
        type := .builtin .unsignedLongLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLongLong, type := .builtin .unsignedLongLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 6⟩)

def callableUnsignedLongLongCompoundShiftRightFrameWitness : Bool :=
  unsignedLongLongCompoundShiftRightFrame

#guard callableUnsignedLongLongCompoundShiftRightFrameWitness

private def longCompoundAddFrame : Bool :=
  let base := incrementFunction .long "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .long,
        type := .builtin .long})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .long, type := .builtin .long}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 15⟩)

def callableLongCompoundAddFrameWitness : Bool :=
  longCompoundAddFrame

#guard callableLongCompoundAddFrameWitness

private def longCompoundSubtractFrame : Bool :=
  let base := incrementFunction .long "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "-=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .long,
        type := .builtin .long})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .long, type := .builtin .long}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 9⟩)

def callableLongCompoundSubtractFrameWitness : Bool :=
  longCompoundSubtractFrame

#guard callableLongCompoundSubtractFrameWitness

private def longCompoundMultiplyFrame : Bool :=
  let base := incrementFunction .long "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "*=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .long,
        type := .builtin .long})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .long, type := .builtin .long}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 4⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 12⟩)

def callableLongCompoundMultiplyFrameWitness : Bool :=
  longCompoundMultiplyFrame

#guard callableLongCompoundMultiplyFrameWitness

private def longCompoundDivideFrame : Bool :=
  let base := incrementFunction .long "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "/=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .long,
        type := .builtin .long})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .long, type := .builtin .long}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 4⟩)

def callableLongCompoundDivideFrameWitness : Bool :=
  longCompoundDivideFrame

#guard callableLongCompoundDivideFrameWitness

private def longCompoundModuloFrame : Bool :=
  let base := incrementFunction .long "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "%=" (handle "0x10")
      {expression := .integer 5, sourceType := .builtin .long,
        type := .builtin .long})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .long, type := .builtin .long}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 3⟩)

def callableLongCompoundModuloFrameWitness : Bool :=
  longCompoundModuloFrame

#guard callableLongCompoundModuloFrameWitness

private def longCompoundBitAndFrame : Bool :=
  let base := incrementFunction .long "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "&=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .long,
        type := .builtin .long})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .long, type := .builtin .long}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 1⟩)

def callableLongCompoundBitAndFrameWitness : Bool :=
  longCompoundBitAndFrame

#guard callableLongCompoundBitAndFrameWitness

private def longCompoundBitOrFrame : Bool :=
  let base := incrementFunction .long "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "|=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .long,
        type := .builtin .long})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .long, type := .builtin .long}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 15⟩)

def callableLongCompoundBitOrFrameWitness : Bool :=
  longCompoundBitOrFrame

#guard callableLongCompoundBitOrFrameWitness

private def longCompoundBitXorFrame : Bool :=
  let base := incrementFunction .long "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "^=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .long,
        type := .builtin .long})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .long, type := .builtin .long}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 15⟩)

def callableLongCompoundBitXorFrameWitness : Bool :=
  longCompoundBitXorFrame

#guard callableLongCompoundBitXorFrameWitness

private def longCompoundShiftLeftFrame : Bool :=
  let base := incrementFunction .long "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "<<=" (handle "0x10")
      {expression := .integer 2, sourceType := .builtin .long,
        type := .builtin .long})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .long, type := .builtin .long}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 3⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 12⟩)

def callableLongCompoundShiftLeftFrameWitness : Bool :=
  longCompoundShiftLeftFrame

#guard callableLongCompoundShiftLeftFrameWitness

private def longCompoundShiftRightFrame : Bool :=
  let base := incrementFunction .long "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign ">>=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .long,
        type := .builtin .long})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .long, type := .builtin .long}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 6⟩)

def callableLongCompoundShiftRightFrameWitness : Bool :=
  longCompoundShiftRightFrame

#guard callableLongCompoundShiftRightFrameWitness

private def unsignedLongCompoundAddFrame : Bool :=
  let base := incrementFunction .unsignedLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLong,
        type := .builtin .unsignedLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLong, type := .builtin .unsignedLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 15⟩)

def callableUnsignedLongCompoundAddFrameWitness : Bool :=
  unsignedLongCompoundAddFrame

#guard callableUnsignedLongCompoundAddFrameWitness

private def unsignedLongCompoundSubtractFrame : Bool :=
  let base := incrementFunction .unsignedLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "-=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLong,
        type := .builtin .unsignedLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLong, type := .builtin .unsignedLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 9⟩)

def callableUnsignedLongCompoundSubtractFrameWitness : Bool :=
  unsignedLongCompoundSubtractFrame

#guard callableUnsignedLongCompoundSubtractFrameWitness

private def unsignedLongCompoundMultiplyFrame : Bool :=
  let base := incrementFunction .unsignedLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "*=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLong,
        type := .builtin .unsignedLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLong, type := .builtin .unsignedLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 4⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 12⟩)

def callableUnsignedLongCompoundMultiplyFrameWitness : Bool :=
  unsignedLongCompoundMultiplyFrame

#guard callableUnsignedLongCompoundMultiplyFrameWitness

private def unsignedLongCompoundDivideFrame : Bool :=
  let base := incrementFunction .unsignedLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "/=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLong,
        type := .builtin .unsignedLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLong, type := .builtin .unsignedLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 4⟩)

def callableUnsignedLongCompoundDivideFrameWitness : Bool :=
  unsignedLongCompoundDivideFrame

#guard callableUnsignedLongCompoundDivideFrameWitness

private def unsignedLongCompoundModuloFrame : Bool :=
  let base := incrementFunction .unsignedLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "%=" (handle "0x10")
      {expression := .integer 5, sourceType := .builtin .unsignedLong,
        type := .builtin .unsignedLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLong, type := .builtin .unsignedLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 3⟩)

def callableUnsignedLongCompoundModuloFrameWitness : Bool :=
  unsignedLongCompoundModuloFrame

#guard callableUnsignedLongCompoundModuloFrameWitness

private def unsignedLongCompoundBitAndFrame : Bool :=
  let base := incrementFunction .unsignedLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "&=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLong,
        type := .builtin .unsignedLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLong, type := .builtin .unsignedLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 1⟩)

def callableUnsignedLongCompoundBitAndFrameWitness : Bool :=
  unsignedLongCompoundBitAndFrame

#guard callableUnsignedLongCompoundBitAndFrameWitness

private def unsignedLongCompoundBitOrFrame : Bool :=
  let base := incrementFunction .unsignedLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "|=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLong,
        type := .builtin .unsignedLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLong, type := .builtin .unsignedLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 15⟩)

def callableUnsignedLongCompoundBitOrFrameWitness : Bool :=
  unsignedLongCompoundBitOrFrame

#guard callableUnsignedLongCompoundBitOrFrameWitness

private def unsignedLongCompoundBitXorFrame : Bool :=
  let base := incrementFunction .unsignedLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "^=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .unsignedLong,
        type := .builtin .unsignedLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLong, type := .builtin .unsignedLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 15⟩)

def callableUnsignedLongCompoundBitXorFrameWitness : Bool :=
  unsignedLongCompoundBitXorFrame

#guard callableUnsignedLongCompoundBitXorFrameWitness

private def unsignedLongCompoundShiftLeftFrame : Bool :=
  let base := incrementFunction .unsignedLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "<<=" (handle "0x10")
      {expression := .integer 2, sourceType := .builtin .unsignedLong,
        type := .builtin .unsignedLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLong, type := .builtin .unsignedLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 3⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 12⟩)

def callableUnsignedLongCompoundShiftLeftFrameWitness : Bool :=
  unsignedLongCompoundShiftLeftFrame

#guard callableUnsignedLongCompoundShiftLeftFrameWitness

private def unsignedLongCompoundShiftRightFrame : Bool :=
  let base := incrementFunction .unsignedLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign ">>=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .unsignedLong,
        type := .builtin .unsignedLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .unsignedLong, type := .builtin .unsignedLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.unsigned 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.unsigned 64, 6⟩)

def callableUnsignedLongCompoundShiftRightFrameWitness : Bool :=
  unsignedLongCompoundShiftRightFrame

#guard callableUnsignedLongCompoundShiftRightFrameWitness

private def longLongCompoundAddFrame : Bool :=
  let base := incrementFunction .longLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "+=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .longLong,
        type := .builtin .longLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .longLong, type := .builtin .longLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 15⟩)

def callableLongLongCompoundAddFrameWitness : Bool :=
  longLongCompoundAddFrame

#guard callableLongLongCompoundAddFrameWitness

private def longLongCompoundSubtractFrame : Bool :=
  let base := incrementFunction .longLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "-=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .longLong,
        type := .builtin .longLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .longLong, type := .builtin .longLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 9⟩)

def callableLongLongCompoundSubtractFrameWitness : Bool :=
  longLongCompoundSubtractFrame

#guard callableLongLongCompoundSubtractFrameWitness

private def longLongCompoundMultiplyFrame : Bool :=
  let base := incrementFunction .longLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "*=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .longLong,
        type := .builtin .longLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .longLong, type := .builtin .longLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 4⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 12⟩)

def callableLongLongCompoundMultiplyFrameWitness : Bool :=
  longLongCompoundMultiplyFrame

#guard callableLongLongCompoundMultiplyFrameWitness

private def longLongCompoundDivideFrame : Bool :=
  let base := incrementFunction .longLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "/=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .longLong,
        type := .builtin .longLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .longLong, type := .builtin .longLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 4⟩)

def callableLongLongCompoundDivideFrameWitness : Bool :=
  longLongCompoundDivideFrame

#guard callableLongLongCompoundDivideFrameWitness

private def longLongCompoundModuloFrame : Bool :=
  let base := incrementFunction .longLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "%=" (handle "0x10")
      {expression := .integer 5, sourceType := .builtin .longLong,
        type := .builtin .longLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .longLong, type := .builtin .longLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 3⟩)

def callableLongLongCompoundModuloFrameWitness : Bool :=
  longLongCompoundModuloFrame

#guard callableLongLongCompoundModuloFrameWitness

private def longLongCompoundBitAndFrame : Bool :=
  let base := incrementFunction .longLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "&=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .longLong,
        type := .builtin .longLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .longLong, type := .builtin .longLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 1⟩)

def callableLongLongCompoundBitAndFrameWitness : Bool :=
  longLongCompoundBitAndFrame

#guard callableLongLongCompoundBitAndFrameWitness

private def longLongCompoundBitOrFrame : Bool :=
  let base := incrementFunction .longLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "|=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .longLong,
        type := .builtin .longLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .longLong, type := .builtin .longLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 15⟩)

def callableLongLongCompoundBitOrFrameWitness : Bool :=
  longLongCompoundBitOrFrame

#guard callableLongLongCompoundBitOrFrameWitness

private def longLongCompoundBitXorFrame : Bool :=
  let base := incrementFunction .longLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "^=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .longLong,
        type := .builtin .longLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .longLong, type := .builtin .longLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 15⟩)

def callableLongLongCompoundBitXorFrameWitness : Bool :=
  longLongCompoundBitXorFrame

#guard callableLongLongCompoundBitXorFrameWitness

private def longLongCompoundShiftLeftFrame : Bool :=
  let base := incrementFunction .longLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "<<=" (handle "0x10")
      {expression := .integer 2, sourceType := .builtin .longLong,
        type := .builtin .longLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .longLong, type := .builtin .longLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 3⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 12⟩)

def callableLongLongCompoundShiftLeftFrameWitness : Bool :=
  longLongCompoundShiftLeftFrame

#guard callableLongLongCompoundShiftLeftFrameWitness

private def longLongCompoundShiftRightFrame : Bool :=
  let base := incrementFunction .longLong "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign ">>=" (handle "0x10")
      {expression := .integer 1, sourceType := .builtin .longLong,
        type := .builtin .longLong})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .longLong, type := .builtin .longLong}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 64, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 64, 6⟩)

def callableLongLongCompoundShiftRightFrameWitness : Bool :=
  longLongCompoundShiftRightFrame

#guard callableLongLongCompoundShiftRightFrameWitness

private def intCompoundBitAndFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "&=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .int,
        type := .builtin .int})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .int, type := .builtin .int}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 32, 13⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 32, 1⟩)

def callableIntCompoundBitAndFrameWitness : Bool :=
  intCompoundBitAndFrame

#guard callableIntCompoundBitAndFrameWitness

private def intCompoundBitOrFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "|=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .int,
        type := .builtin .int})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .int, type := .builtin .int}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 32, 15⟩)

def callableIntCompoundBitOrFrameWitness : Bool :=
  intCompoundBitOrFrame

#guard callableIntCompoundBitOrFrameWitness

private def intCompoundBitXorFrame : Bool :=
  let base := incrementFunction .int "++" false
  let function := {base with body := .block (.sequence
    (.compoundAssign "^=" (handle "0x10")
      {expression := .integer 3, sourceType := .builtin .int,
        type := .builtin .int})
    (.return_ {
      expression := .parameter (handle "0x10"),
      sourceType := .builtin .int, type := .builtin .int}))}
  match CallableObjectFrame.start .lp64 function [⟨.signed 32, 12⟩] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 32 started
      outcome.result matches .ok (.ok ⟨.signed 32, 15⟩)

def callableIntCompoundBitXorFrameWitness : Bool :=
  intCompoundBitXorFrame

#guard callableIntCompoundBitXorFrameWitness

-- No native oracle execution is run for signed overflow. The failed arithmetic
-- leaves the live parameter unchanged in both prefix and postfix cases.
private def overflowRetainsParameter (operator : String) (isPostfix : Bool) (value : Int) : Bool :=
  match CallableObjectFrame.start .lp64 (incrementFunction .int operator isPostfix) [signed value] with
  | .error _ => false
  | .ok started =>
      let outcome := evaluateCallableObjectInFrame 16 started
      outcome.result.toOption == some (.undefined .signedOverflow) &&
        (outcome.frame.read (handle "0x10")).result.toOption == some (signed value)

def callableSignedOverflowFrameWitness : Bool :=
  overflowRetainsParameter "++" false 2147483647

def callableSignedPostfixOverflowFrameWitness : Bool :=
  overflowRetainsParameter "++" true 2147483647

def callableSignedDecrementOverflowFrameWitness : Bool :=
  overflowRetainsParameter "--" false (-2147483648)

def callableSignedPostfixDecrementOverflowFrameWitness : Bool :=
  overflowRetainsParameter "--" true (-2147483648)

#guard postfixStore
#guard callablePostfixStoreWitness
#guard callableUnsignedFrameIncrementWitness
#guard callableUnsignedPostfixStoreWitness
#guard callableUnsignedFrameDecrementWitness
#guard callableUnsignedPostfixDecrementStoreWitness
#guard callableUnsignedPostfixReturnWitness
#guard callableUnsignedCompoundFrameWitness
#guard callableSignedOverflowFrameWitness
#guard callableSignedPostfixOverflowFrameWitness
#guard callableSignedDecrementOverflowFrameWitness
#guard callableSignedPostfixDecrementOverflowFrameWitness
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

def callableKernelDoWhileFrameWitness : Bool :=
  kernelControl (.doWhile controlStep controlParameter)

def callableKernelForFrameWitness : Bool :=
  kernelControl (.forLoop .skip controlParameter controlStep
    (.switch_ controlParameter [
      {label := some 3, body := .continue_},
      {label := some 2, body := .skip},
      {label := none, body := .break_}]))

def callableFuelExhaustionWitness : Bool :=
  let callable : CallableFunction := {
    functionWithLocal (.literal (signed 0)) with
      body := .block (.return_ {
        expression := .parameter (handle "0x10"),
        sourceType := intType, type := intType})}
  match CallableObjectFrame.start .lp64 callable [signed 7] with
  | .error _ => false
  | .ok started =>
      (evaluateCallableObjectInFrame 0 started).result matches
        .error (.frameError .fuelExhausted)

private theorem kernelControlExecution :
    (kernelControl (.doWhile controlStep controlParameter) &&
      kernelControl (.forLoop .skip controlParameter controlStep
        (.switch_ controlParameter [
          {label := some 3, body := .continue_},
          {label := some 2, body := .skip},
          {label := none, body := .break_}])) &&
      checkIncrement .short "++" false ⟨.signed 16, 32767⟩ ⟨.signed 16, -32768⟩) = true := rfl

#print axioms kernelControlExecution

#guard callableKernelDoWhileFrameWitness
#guard callableKernelForFrameWitness
#guard callableFuelExhaustionWitness
#guard callableSelfInitializerFailureWitness

end LeanModels.Cpp.CallableObjectEvaluationTests
