import LeanModels.Cpp.CallableRefinement

namespace LeanModels.Cpp.CallableRefinementTests

open CallableObjectEvaluation

private def handle : FrontendHandle := {value := "0x10"}
private def intType : CppTypeEvidence := .builtin .int
private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩
private def parameter : CallableParameter := {declaration := handle, name := some "x", type := intType}
private def declaration : Declaration := {
  id := "0x2", kind := "FunctionDecl", path := [0], name := some "identity",
  lexicalParents := [], semanticParent := none, previousDecl := none,
  mangledName := none, type := none, location := none, range := none}
private def expression : TypedCallableExpression := {
  expression := .parameter handle, sourceType := intType, type := intType}
private def function : CallableFunction := {
  occurrence := declaration,
  signature := {result := intType, parameters := [intType], variadic := false},
  parameters := [parameter], body := .return_ expression}

private def sampleFrame : IntegralObjectFrame :=
  match CallableObjectFrame.start .lp64 function [signed (-128)] with
  | .ok callable => callable.frame
  | .error _ => default

/-- A concrete initialized frame discharges every premise of the symbolic
parameter-expression agreement theorem. -/
theorem sampleParameterExpressionAgreement :
    evaluateCallableExpression 9 .lp64 [parameter] [signed (-128)] expression =
      .ok (.ok (signed (-128)), [signed (-128)]) ∧
    evaluateCallableObjectExpression 9 .lp64 sampleFrame expression =
      {frame := sampleFrame, result := .ok (.ok (signed (-128)))} := by
  exact callableParameterExpressionAgreement 7 .lp64 [parameter] [signed (-128)]
    sampleFrame handle 0 parameter (signed (-128)) intType intType
    rfl rfl rfl rfl rfl rfl rfl

private def parameterReadWitness (n : Int) : Bool :=
  let value := signed n
  match CallableObjectFrame.start .lp64 function [value] with
  | .error _ => false
  | .ok callable =>
      let read := callable.frame.evaluate 1 (.read handle)
      let object := evaluateCallableObjectExpression 9 .lp64 callable.frame expression
      match read.result,
          evaluateCallableExpression 9 .lp64 [parameter] [value] expression,
          object.result with
      | .ok (.ok readValue), .ok (.ok valueResult, arguments), .ok (.ok objectResult) =>
          readValue == value && valueResult == value && objectResult == value &&
            arguments == [value] && read.frame == callable.frame && object.frame == callable.frame
      | _, _, _ => false

def callableParameterExpressionAgreementWitness : Bool :=
  [-128, 0, 2147483647].all parameterReadWitness

#guard callableParameterExpressionAgreementWitness

end LeanModels.Cpp.CallableRefinementTests
