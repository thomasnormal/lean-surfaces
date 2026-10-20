import LeanModels.Cpp.CallableObjectEvaluation
import LeanModels.Cpp.CallableEvaluation

namespace LeanModels.Cpp.CallableObjectEvaluationTests

open CallableObjectEvaluation
open IntegralObjectFrame

private def handle (value : String) : FrontendHandle := {value}
private def intType : CppTypeEvidence := .builtin .int
private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩

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

private def readsParameter : Bool :=
  match evaluateCallableObject 32 .lp64 (functionWithLocal (.read (handle "0x10"))) [signed 7] with
  | .ok (.ok value) => value == signed 7
  | _ => false

private def valueOnlyRemainsLoud : Bool :=
  match evaluateCallable 32 .lp64 (functionWithLocal (.read (handle "0x10"))) [signed 7] with
  | .error .unsupportedDeclaration => true
  | _ => false

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
      [localEvidence] [] .lp64 intType [parameter] statement with
  | .ok (.automatic admitted, scope) =>
      admitted.declarations == [declaration] &&
        scope.any (fun current => current.declaration == declaration)
  | _ => false

#guard readsParameter
#guard valueOnlyRemainsLoud
#guard selfInitializerRetainsFrame
#guard nestedBlockDropsLocal
#guard localMutation
#guard localIncrement
#guard loopLocalReentry
#guard parserAdmitsAutomaticLocal

end LeanModels.Cpp.CallableObjectEvaluationTests
