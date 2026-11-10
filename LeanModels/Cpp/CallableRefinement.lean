import LeanModels.Cpp.CallableEvaluation
import LeanModels.Cpp.CallableObjectEvaluation

namespace LeanModels.Cpp

open CallableObjectEvaluation

/-- Agreement is preserved by a conversion whose destination format resolves.
The operand may update either state; conversion retains both updated states.
Non-value integral results are propagated on both sides. -/
theorem callableConvertExpressionAgreement (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments arguments' : List IntegralValue)
    (frame frame' : IntegralObjectFrame) (operand : TypedCallableExpression)
    (sourceType resultType : CppTypeEvidence) (fmt : IntegralFormat)
    (result : IntegralResult IntegralValue)
    (hvalue : evaluateCallableExpression fuel profile parameters arguments operand =
      .ok (result, arguments'))
    (hobject : evaluateCallableObjectExpression fuel profile frame operand =
      {frame := frame', result := .ok result})
    (hformat : integralFormatOfEvidence profile resultType = .ok fmt) :
    let expression : TypedCallableExpression :=
      {expression := .convert operand, sourceType := sourceType, type := resultType}
    evaluateCallableExpression (fuel + 1) profile parameters arguments expression =
      .ok (bindIntegralResultValue result (integralConvert fmt), arguments') ∧
    evaluateCallableObjectExpression (fuel + 1) profile frame expression =
      {frame := frame', result := .ok (bindIntegralResultValue result (integralConvert fmt))} := by
  exact ⟨evaluateCallableExpression_convert fuel profile parameters arguments arguments' operand
    sourceType resultType fmt result hvalue hformat,
    evaluateCallableObjectExpression_convert fuel profile frame frame' operand sourceType resultType
      fmt result hobject hformat⟩

/-- Related literal evaluations return the same integral result, including
invalid values, and preserve the argument list and object frame. The source
literal and result type must resolve to the stated common format. -/
theorem callableLiteralExpressionAgreement (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments : List IntegralValue)
    (frame : IntegralObjectFrame) (n : Nat) (value : IntegralValue)
    (sourceType resultType : CppTypeEvidence)
    (hsource : integralLiteralOfEvidence profile sourceType n = .ok value)
    (hresult : integralFormatOfEvidence profile resultType = .ok value.format) :
    let expression : TypedCallableExpression :=
      {expression := .integer n, sourceType := sourceType, type := resultType}
    evaluateCallableExpression (fuel + 1) profile parameters arguments expression =
      .ok (integralConvert value.format value, arguments) ∧
    evaluateCallableObjectExpression (fuel + 1) profile frame expression =
      {frame := frame, result := .ok (integralConvert value.format value)} := by
  exact ⟨evaluateCallableExpression_literal fuel profile parameters arguments n value
    sourceType resultType hsource,
    evaluateCallableObjectExpression_literal fuel profile frame n value sourceType resultType
      hsource hresult⟩

/-- A related value argument and object-frame read have the same parameter
expression result and preserve their respective states. The frame-read premise
is the relation between the two representations; it is not established by
this lemma. This is one expression case, not a whole-call refinement. -/
theorem callableParameterExpressionAgreement (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments : List IntegralValue)
    (frame : IntegralObjectFrame) (declaration : FrontendHandle) (index : Nat)
    (param : CallableParameter) (value : IntegralValue)
    (sourceType resultType : CppTypeEvidence)
    (hidx : parameters.findIdx? (fun p => p.declaration == declaration) = some index)
    (hp : parameters[index]? = some param) (ha : arguments[index]? = some value)
    (hparam : integralFormatOfEvidence profile param.type = .ok value.format)
    (hresult : integralFormatOfEvidence profile resultType = .ok value.format)
    (hvalid : value.invalid? = none)
    (hread : frame.evaluate 1 (.read declaration) =
      {frame := frame, result := .ok (.ok value)}) :
    let expression : TypedCallableExpression :=
      {expression := .parameter declaration, sourceType := sourceType, type := resultType}
    evaluateCallableExpression (fuel + 2) profile parameters arguments expression =
      .ok (.ok value, arguments) ∧
    evaluateCallableObjectExpression (fuel + 2) profile frame expression =
      {frame := frame, result := .ok (.ok value)} := by
  constructor
  · simpa [Nat.add_assoc] using
      evaluateCallableExpression_parameter (fuel + 1) profile parameters arguments declaration index
        param value sourceType resultType hidx hp ha hparam hresult hvalid
  · exact evaluateCallableObjectExpression_parameter fuel profile frame declaration value
      sourceType resultType hread hresult hvalid

end LeanModels.Cpp
