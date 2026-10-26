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
