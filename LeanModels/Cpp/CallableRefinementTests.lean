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

private def increment : TypedCallableExpression := {
  expression := .increment "++" false handle, sourceType := intType, type := intType}
private def seventeen : TypedCallableExpression := {
  expression := .integer 17, sourceType := intType, type := intType}
private def conditional : TypedCallableExpression := {
  expression := .conditional expression increment seventeen, sourceType := intType, type := intType}
private def frameAfterIncrement : IntegralObjectFrame :=
  (evaluateCallableObjectExpression 8 .lp64 sampleFrame increment).frame

/-- The conditional theorem composes parameter agreement with a branch that
mutates the parameter in both representations. -/
theorem sampleConditionalExpressionAgreement :
    evaluateCallableExpression 9 .lp64 [parameter] [signed (-128)] conditional =
      .ok (.ok (signed (-127)), [signed (-127)]) ∧
    evaluateCallableObjectExpression 9 .lp64 sampleFrame conditional =
      {frame := frameAfterIncrement, result := .ok (.ok (signed (-127)))} := by
  have hcond := callableParameterExpressionAgreement 6 .lp64 [parameter] [signed (-128)]
    sampleFrame handle 0 parameter (signed (-128)) intType intType
    rfl rfl rfl rfl rfl rfl rfl
  exact callableConditionalExpressionAgreement 8 .lp64 [parameter] [signed (-128)]
    [signed (-128)] [signed (-127)] sampleFrame sampleFrame frameAfterIncrement
    expression increment seventeen intType intType (signed (-128)) (.ok (signed (-127)))
    hcond.1 hcond.2 rfl rfl

private def missingParameter : TypedCallableExpression := {
  expression := .parameter {value := "missing"}, sourceType := intType, type := intType}

/-- A non-value condition bypasses both branches, even when either would fail. -/
theorem invalidConditionalExpressionAgreement :
    let condition : TypedCallableExpression := {
      expression := .integer 2147483648, sourceType := intType, type := intType}
    let conditional : TypedCallableExpression := {
      expression := .conditional condition missingParameter missingParameter,
      sourceType := intType, type := intType}
    evaluateCallableExpression 9 .lp64 [] [] conditional = .ok (.invalid .outOfRange, []) ∧
    evaluateCallableObjectExpression 9 .lp64 sampleFrame conditional =
      {frame := sampleFrame, result := .ok (.invalid .outOfRange)} := by
  exact callableConditionalExpressionAgreement_nonvalue 8 .lp64 [] [] [] sampleFrame sampleFrame
    {expression := .integer 2147483648, sourceType := intType, type := intType}
    missingParameter missingParameter intType intType (.invalid .outOfRange)
    (by intro v h; cases h) invalidLiteralExpressionAgreement.1 invalidLiteralExpressionAgreement.2

private def conditionalWitness (n : Int) : Bool :=
  let value := signed n
  match CallableObjectFrame.start .lp64 function [value] with
  | .error _ => false
  | .ok callable =>
      let expectedArgument := signed (if n == 0 then 0 else n + 1)
      let expectedResult := signed (if n == 0 then 17 else n + 1)
      let object := evaluateCallableObjectExpression 9 .lp64 callable.frame conditional
      let after := object.frame.evaluate 1 (.read handle)
      match evaluateCallableExpression 9 .lp64 [parameter] [value] conditional,
          object.result, after.result with
      | .ok (.ok a, arguments), .ok (.ok b), .ok (.ok finalValue) =>
          a == expectedResult && b == expectedResult && arguments == [expectedArgument] &&
            finalValue == expectedArgument
      | _, _, _ => false

def callableConditionalExpressionAgreementWitness : Bool :=
  [-128, 0, 5].all conditionalWitness

#guard callableConditionalExpressionAgreementWitness

private def nestedCondition : TypedCallableExpression := {
  expression := .integer 1, sourceType := intType, type := intType}
private def nestedOperand : TypedCallableExpression := {
  expression := .integer 257, sourceType := intType, type := intType}
private def nestedTrue : TypedCallableExpression := {
  expression := .convert nestedOperand, sourceType := intType, type := unsignedCharType}
private def nestedFalse : TypedCallableExpression := {
  expression := .convert seventeen, sourceType := intType, type := unsignedCharType}
private def nestedExpression : TypedCallableExpression := {
  expression := .conditional nestedCondition nestedTrue nestedFalse,
  sourceType := unsignedCharType, type := unsignedCharType}

/-- A nested conditional and conversion is derived structurally, then both
evaluator results follow from the derivation's soundness theorem. -/
theorem nestedExpressionDerivation :
    CallableExpressionDerivation .lp64 [] 9 [] sampleFrame nestedExpression
      (.ok ⟨.unsigned 8, 1⟩) [] sampleFrame := by
  apply CallableExpressionDerivation.conditional 8 [] [] [] sampleFrame sampleFrame sampleFrame
    nestedCondition nestedTrue nestedFalse unsignedCharType unsignedCharType
    (signed 1) (.ok ⟨.unsigned 8, 1⟩)
  · exact CallableExpressionDerivation.literal 7 [] sampleFrame 1 (signed 1) intType intType rfl rfl
  · exact CallableExpressionDerivation.convert 7 [] [] sampleFrame sampleFrame nestedOperand
      intType unsignedCharType (.unsigned 8) (.ok (signed 257))
      (CallableExpressionDerivation.literal 6 [] sampleFrame 257 (signed 257) intType intType rfl rfl)
      rfl

theorem nestedExpressionAgreement :
    evaluateCallableExpression 9 .lp64 [] [] nestedExpression =
      .ok (.ok ⟨.unsigned 8, 1⟩, []) ∧
    evaluateCallableObjectExpression 9 .lp64 sampleFrame nestedExpression =
      {frame := sampleFrame, result := .ok (.ok ⟨.unsigned 8, 1⟩)} :=
  nestedExpressionDerivation.sound

/-- A related parameter can also be used as the condition in a derivation. -/
theorem parameterConditionalDerivation :
    let zero : TypedCallableExpression := {
      expression := .integer 0, sourceType := intType, type := intType}
    CallableExpressionDerivation .lp64 [parameter] 9 [signed (-128)] sampleFrame
      {expression := .conditional expression seventeen zero, sourceType := intType, type := intType}
      (.ok (signed 17)) [signed (-128)] sampleFrame := by
  exact CallableExpressionDerivation.conditional 8 [signed (-128)] [signed (-128)]
    [signed (-128)] sampleFrame sampleFrame sampleFrame expression seventeen
    {expression := .integer 0, sourceType := intType, type := intType} intType intType
    (signed (-128)) (.ok (signed 17))
    (CallableExpressionDerivation.parameter 6 [signed (-128)] sampleFrame handle 0 parameter
      (signed (-128)) intType intType rfl rfl rfl rfl rfl rfl rfl)
    (CallableExpressionDerivation.literal 7 [signed (-128)] sampleFrame 17 (signed 17)
      intType intType rfl rfl)

/-- The structural rule for a non-value condition does not require either
unselected branch to have a derivation. -/
theorem invalidConditionalDerivation :
    CallableExpressionDerivation .lp64 [] 9 [] sampleFrame
      {expression := .conditional
        {expression := .integer 2147483648, sourceType := intType, type := intType}
        missingParameter missingParameter, sourceType := intType, type := intType}
      (.invalid .outOfRange) [] sampleFrame := by
  exact CallableExpressionDerivation.conditionalNonvalue 8 [] [] sampleFrame sampleFrame
    {expression := .integer 2147483648, sourceType := intType, type := intType}
    missingParameter missingParameter intType intType (.invalid .outOfRange)
    (by intro v h; cases h)
    (CallableExpressionDerivation.literal 7 [] sampleFrame 2147483648
      (signed 2147483648) intType intType rfl rfl)

def callableNestedDerivationWitness : Bool :=
  let object := evaluateCallableObjectExpression 9 .lp64 sampleFrame nestedExpression
  match evaluateCallableExpression 9 .lp64 [] [] nestedExpression, object.result with
  | .ok (.ok a, []), .ok (.ok b) =>
      a == ⟨.unsigned 8, 1⟩ && b == ⟨.unsigned 8, 1⟩ && object.frame == sampleFrame
  | _, _ => false

#guard callableNestedDerivationWitness

/-- Both branches are described by the pure fragment, not by assumed
evaluator outcomes. -/
theorem nestedExpressionPure : CallablePureExpression .lp64 9 nestedExpression := by
  apply CallablePureExpression.conditional 8 nestedCondition nestedTrue nestedFalse
    unsignedCharType unsignedCharType
  · exact CallablePureExpression.literal 7 1 (signed 1) intType intType rfl rfl
  · exact CallablePureExpression.convert 7 nestedOperand intType unsignedCharType (.unsigned 8)
      (CallablePureExpression.literal 6 257 (signed 257) intType intType rfl rfl) rfl
  · exact CallablePureExpression.convert 7 seventeen intType unsignedCharType (.unsigned 8)
      (CallablePureExpression.literal 6 17 (signed 17) intType intType rfl rfl) rfl

theorem nestedPureAgreement :
    ∃ result, evaluateCallableExpression 9 .lp64 [] [] nestedExpression = .ok (result, []) ∧
      evaluateCallableObjectExpression 9 .lp64 sampleFrame nestedExpression =
        {frame := sampleFrame, result := .ok result} :=
  nestedExpressionPure.agreement [] [] sampleFrame

private def castChain : Nat → TypedCallableExpression
  | 0 => {expression := .integer 7, sourceType := intType, type := intType}
  | n + 1 => {expression := .convert (castChain n), sourceType := intType, type := intType}

/-- The fragment and its agreement theorem apply at arbitrary expression
depth, rather than to a fixed list of examples. -/
theorem castChainPure (n : Nat) : CallablePureExpression .lp64 (n + 1) (castChain n) := by
  induction n with
  | zero => exact CallablePureExpression.literal 0 7 (signed 7) intType intType rfl rfl
  | succ n ih =>
      exact CallablePureExpression.convert (n + 1) (castChain n) intType intType (.signed 32) ih rfl

theorem castChainAgreement (n : Nat) (arguments : List IntegralValue) (frame : IntegralObjectFrame) :
    ∃ result, evaluateCallableExpression (n + 1) .lp64 [] arguments (castChain n) =
        .ok (result, arguments) ∧
      evaluateCallableObjectExpression (n + 1) .lp64 frame (castChain n) =
        {frame := frame, result := .ok result} :=
  (castChainPure n).agreement [] arguments frame

def callablePureCastChainWitness : Bool :=
  let expression := castChain 4
  let object := evaluateCallableObjectExpression 5 .lp64 sampleFrame expression
  match evaluateCallableExpression 5 .lp64 [] [] expression, object.result with
  | .ok (.ok a, []), .ok (.ok b) => a == signed 7 && b == signed 7 && object.frame == sampleFrame
  | _, _ => false

#guard callablePureCastChainWitness

end LeanModels.Cpp.CallableRefinementTests
