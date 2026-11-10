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

/-- Even an out-of-range literal has the same invalid result in both
expression evaluators; this constructed IR is not an admitted C++ literal. -/
theorem invalidLiteralExpressionAgreement :
    evaluateCallableExpression 8 .lp64 [] []
      {expression := .integer 2147483648, sourceType := intType, type := intType} =
      .ok (.invalid .outOfRange, []) ∧
    evaluateCallableObjectExpression 8 .lp64 sampleFrame
      {expression := .integer 2147483648, sourceType := intType, type := intType} =
      {frame := sampleFrame, result := .ok (.invalid .outOfRange)} := by
  exact callableLiteralExpressionAgreement 7 .lp64 [] [] sampleFrame 2147483648
    (signed 2147483648) intType intType rfl rfl

private def literalReadWitness (n : Nat) : Bool :=
  let value : IntegralValue := ⟨.signed 32, n⟩
  let expression : TypedCallableExpression := {
    expression := .integer n, sourceType := intType, type := intType}
  let object := evaluateCallableObjectExpression 8 .lp64 sampleFrame expression
  match evaluateCallableExpression 8 .lp64 [] [] expression, object.result with
  | .ok (.ok a, []), .ok (.ok b) =>
      a == value && b == value && object.frame == sampleFrame
  | _, _ => false

def callableLiteralExpressionAgreementWitness : Bool :=
  [0, 7, 2147483647].all literalReadWitness

#guard callableLiteralExpressionAgreementWitness

private def unsignedCharType : CppTypeEvidence := .builtin .unsignedChar

/-- The conversion rule composes with literal agreement; 257 converts to 1. -/
theorem sampleConvertExpressionAgreement :
    let operand : TypedCallableExpression := {
      expression := .integer 257, sourceType := intType, type := intType}
    let converted : TypedCallableExpression := {
      expression := .convert operand, sourceType := intType, type := unsignedCharType}
    evaluateCallableExpression 9 .lp64 [] [] converted =
      .ok (.ok ⟨.unsigned 8, 1⟩, []) ∧
    evaluateCallableObjectExpression 9 .lp64 sampleFrame converted =
      {frame := sampleFrame, result := .ok (.ok ⟨.unsigned 8, 1⟩)} := by
  have hlit := callableLiteralExpressionAgreement 7 .lp64 [] [] sampleFrame 257
    (signed 257) intType intType rfl rfl
  exact callableConvertExpressionAgreement 8 .lp64 [] [] [] sampleFrame sampleFrame
    {expression := .integer 257, sourceType := intType, type := intType}
    intType unsignedCharType (.unsigned 8) (.ok (signed 257)) hlit.1 hlit.2 rfl

/-- A malformed out-of-range literal's invalid result survives conversion. -/
theorem invalidConvertExpressionAgreement :
    let operand : TypedCallableExpression := {
      expression := .integer 2147483648, sourceType := intType, type := intType}
    let converted : TypedCallableExpression := {
      expression := .convert operand, sourceType := intType, type := unsignedCharType}
    evaluateCallableExpression 9 .lp64 [] [] converted = .ok (.invalid .outOfRange, []) ∧
    evaluateCallableObjectExpression 9 .lp64 sampleFrame converted =
      {frame := sampleFrame, result := .ok (.invalid .outOfRange)} := by
  exact callableConvertExpressionAgreement 8 .lp64 [] [] [] sampleFrame sampleFrame
    {expression := .integer 2147483648, sourceType := intType, type := intType}
    intType unsignedCharType (.unsigned 8) (.invalid .outOfRange)
    invalidLiteralExpressionAgreement.1 invalidLiteralExpressionAgreement.2 rfl

private def conversionWitness (n : Nat) : Bool :=
  let operand : TypedCallableExpression := {
    expression := .integer n, sourceType := intType, type := intType}
  let converted : TypedCallableExpression := {
    expression := .convert operand, sourceType := intType, type := unsignedCharType}
  let expected : IntegralValue := ⟨.unsigned 8, n % 256⟩
  let object := evaluateCallableObjectExpression 9 .lp64 sampleFrame converted
  match evaluateCallableExpression 9 .lp64 [] [] converted, object.result with
  | .ok (.ok a, []), .ok (.ok b) =>
      a == expected && b == expected && object.frame == sampleFrame
  | _, _ => false

def callableConvertExpressionAgreementWitness : Bool :=
  [0, 255, 256, 257].all conversionWitness

#guard callableConvertExpressionAgreementWitness

end LeanModels.Cpp.CallableRefinementTests
