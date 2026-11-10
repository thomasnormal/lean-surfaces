import LeanModels.Cpp.CallableEvaluation
import LeanModels.Cpp.CallableObjectEvaluation

namespace LeanModels.Cpp

open CallableObjectEvaluation

/-- Agreement on a successful condition and its selected branch carries
through a conditional expression, retaining each computation's final state. -/
theorem callableConditionalExpressionAgreement (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments afterCondition afterBranch : List IntegralValue)
    (frame frameAfterCondition frameAfterBranch : IntegralObjectFrame)
    (condition whenTrue whenFalse : TypedCallableExpression)
    (sourceType resultType : CppTypeEvidence) (value : IntegralValue)
    (result : IntegralResult IntegralValue)
    (hvalueCondition : evaluateCallableExpression fuel profile parameters arguments condition =
      .ok (.ok value, afterCondition))
    (hobjectCondition : evaluateCallableObjectExpression fuel profile frame condition =
      {frame := frameAfterCondition, result := .ok (.ok value)})
    (hvalueBranch : evaluateCallableExpression fuel profile parameters afterCondition
      (if value.value == 0 then whenFalse else whenTrue) = .ok (result, afterBranch))
    (hobjectBranch : evaluateCallableObjectExpression fuel profile frameAfterCondition
      (if value.value == 0 then whenFalse else whenTrue) =
      {frame := frameAfterBranch, result := .ok result}) :
    let expression : TypedCallableExpression := {
      expression := .conditional condition whenTrue whenFalse,
      sourceType := sourceType, type := resultType}
    evaluateCallableExpression (fuel + 1) profile parameters arguments expression =
      .ok (result, afterBranch) ∧
    evaluateCallableObjectExpression (fuel + 1) profile frame expression =
      {frame := frameAfterBranch, result := .ok result} := by
  exact ⟨evaluateCallableExpression_conditional fuel profile parameters arguments afterCondition
    afterBranch condition whenTrue whenFalse sourceType resultType value result
    hvalueCondition hvalueBranch,
    evaluateCallableObjectExpression_conditional fuel profile frame frameAfterCondition
      frameAfterBranch condition whenTrue whenFalse sourceType resultType value result
      hobjectCondition hobjectBranch⟩

/-- Agreement on a non-value condition propagates without entering a branch. -/
theorem callableConditionalExpressionAgreement_nonvalue (fuel : Nat) (profile : TargetProfile)
    (parameters : List CallableParameter) (arguments afterCondition : List IntegralValue)
    (frame frameAfterCondition : IntegralObjectFrame)
    (condition whenTrue whenFalse : TypedCallableExpression)
    (sourceType resultType : CppTypeEvidence) (result : IntegralResult IntegralValue)
    (hnonvalue : ∀ v, result ≠ .ok v)
    (hvalue : evaluateCallableExpression fuel profile parameters arguments condition =
      .ok (result, afterCondition))
    (hobject : evaluateCallableObjectExpression fuel profile frame condition =
      {frame := frameAfterCondition, result := .ok result}) :
    let expression : TypedCallableExpression := {
      expression := .conditional condition whenTrue whenFalse,
      sourceType := sourceType, type := resultType}
    evaluateCallableExpression (fuel + 1) profile parameters arguments expression =
      .ok (result, afterCondition) ∧
    evaluateCallableObjectExpression (fuel + 1) profile frame expression =
      {frame := frameAfterCondition, result := .ok result} := by
  exact ⟨evaluateCallableExpression_conditional_nonvalue fuel profile parameters arguments
    afterCondition condition whenTrue whenFalse sourceType resultType result hnonvalue hvalue,
    evaluateCallableObjectExpression_conditional_nonvalue fuel profile frame frameAfterCondition
      condition whenTrue whenFalse sourceType resultType result hnonvalue hobject⟩

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

/-- Derivations of a supported expression evaluation. A parameter rule
requires the explicit relation between the value list and the frame. -/
inductive CallableExpressionDerivation (profile : TargetProfile) (parameters : List CallableParameter) :
    Nat → List IntegralValue → IntegralObjectFrame → TypedCallableExpression →
    IntegralResult IntegralValue → List IntegralValue → IntegralObjectFrame → Prop where
  | literal (fuel : Nat) (arguments : List IntegralValue) (frame : IntegralObjectFrame)
      (n : Nat) (value : IntegralValue) (sourceType resultType : CppTypeEvidence)
      (hsource : integralLiteralOfEvidence profile sourceType n = .ok value)
      (hformat : integralFormatOfEvidence profile resultType = .ok value.format) :
      CallableExpressionDerivation profile parameters (fuel + 1) arguments frame
        {expression := .integer n, sourceType := sourceType, type := resultType}
        (integralConvert value.format value) arguments frame
  | parameter (fuel : Nat) (arguments : List IntegralValue) (frame : IntegralObjectFrame)
      (declaration : FrontendHandle) (index : Nat) (param : CallableParameter)
      (value : IntegralValue) (sourceType resultType : CppTypeEvidence)
      (hidx : parameters.findIdx? (fun p => p.declaration == declaration) = some index)
      (hp : parameters[index]? = some param) (ha : arguments[index]? = some value)
      (hparam : integralFormatOfEvidence profile param.type = .ok value.format)
      (hresult : integralFormatOfEvidence profile resultType = .ok value.format)
      (hvalid : value.invalid? = none)
      (hread : frame.evaluate 1 (.read declaration) = {frame := frame, result := .ok (.ok value)}) :
      CallableExpressionDerivation profile parameters (fuel + 2) arguments frame
        {expression := .parameter declaration, sourceType := sourceType, type := resultType}
        (.ok value) arguments frame
  | convert (fuel : Nat) (arguments arguments' : List IntegralValue)
      (frame frame' : IntegralObjectFrame) (operand : TypedCallableExpression)
      (sourceType resultType : CppTypeEvidence) (fmt : IntegralFormat)
      (result : IntegralResult IntegralValue)
      (operandDerivation : CallableExpressionDerivation profile parameters fuel arguments frame operand result arguments' frame')
      (hformat : integralFormatOfEvidence profile resultType = .ok fmt) :
      CallableExpressionDerivation profile parameters (fuel + 1) arguments frame
        {expression := .convert operand, sourceType := sourceType, type := resultType}
        (bindIntegralResultValue result (integralConvert fmt)) arguments' frame'
  | conditional (fuel : Nat) (arguments afterCondition afterBranch : List IntegralValue)
      (frame frameAfterCondition frameAfterBranch : IntegralObjectFrame)
      (condition whenTrue whenFalse : TypedCallableExpression)
      (sourceType resultType : CppTypeEvidence) (value : IntegralValue)
      (result : IntegralResult IntegralValue)
      (conditionDerivation : CallableExpressionDerivation profile parameters fuel arguments frame condition
        (.ok value) afterCondition frameAfterCondition)
      (branchDerivation : CallableExpressionDerivation profile parameters fuel afterCondition frameAfterCondition
        (if value.value == 0 then whenFalse else whenTrue) result afterBranch frameAfterBranch) :
      CallableExpressionDerivation profile parameters (fuel + 1) arguments frame
        {expression := .conditional condition whenTrue whenFalse, sourceType := sourceType, type := resultType}
        result afterBranch frameAfterBranch
  | conditionalNonvalue (fuel : Nat) (arguments afterCondition : List IntegralValue)
      (frame frameAfterCondition : IntegralObjectFrame)
      (condition whenTrue whenFalse : TypedCallableExpression)
      (sourceType resultType : CppTypeEvidence) (result : IntegralResult IntegralValue)
      (hnonvalue : ∀ v, result ≠ .ok v)
      (conditionDerivation : CallableExpressionDerivation profile parameters fuel arguments frame condition
        result afterCondition frameAfterCondition) :
      CallableExpressionDerivation profile parameters (fuel + 1) arguments frame
        {expression := .conditional condition whenTrue whenFalse, sourceType := sourceType, type := resultType}
        result afterCondition frameAfterCondition

theorem CallableExpressionDerivation.sound {profile : TargetProfile} {parameters : List CallableParameter}
    {fuel : Nat} {arguments arguments' : List IntegralValue} {frame frame' : IntegralObjectFrame}
    {expression : TypedCallableExpression} {result : IntegralResult IntegralValue}
    (derivation : CallableExpressionDerivation profile parameters fuel arguments frame expression result arguments' frame') :
    evaluateCallableExpression fuel profile parameters arguments expression = .ok (result, arguments') ∧
      evaluateCallableObjectExpression fuel profile frame expression = {frame := frame', result := .ok result} := by
  induction derivation with
  | literal fuel args frame n value st rt hs hf =>
      exact callableLiteralExpressionAgreement fuel profile parameters args frame n value st rt hs hf
  | parameter fuel args frame decl idx param value st rt hi hp ha hf hr hv hd =>
      exact callableParameterExpressionAgreement fuel profile parameters args frame decl idx param value st rt hi hp ha hf hr hv hd
  | convert fuel args args' frame frame' operand st rt fmt result derivation hf ih =>
      exact callableConvertExpressionAgreement fuel profile parameters args args' frame frame' operand st rt fmt result ih.1 ih.2 hf
  | conditional fuel args mid final frame fm ff cond yes no st rt value result dc db ihc ihb =>
      exact callableConditionalExpressionAgreement fuel profile parameters args mid final frame fm ff cond yes no st rt value result ihc.1 ihc.2 ihb.1 ihb.2
  | conditionalNonvalue fuel args mid frame fm cond yes no st rt result hn dc ih =>
      exact callableConditionalExpressionAgreement_nonvalue fuel profile parameters args mid frame fm cond yes no st rt result hn ih.1 ih.2

/-- A statically described effect-free fragment with a shared depth budget. -/
inductive CallablePureExpression (profile : TargetProfile) : Nat → TypedCallableExpression → Prop where
  | literal (fuel : Nat) (n : Nat) (value : IntegralValue) (sourceType resultType : CppTypeEvidence)
      (hsource : integralLiteralOfEvidence profile sourceType n = .ok value)
      (hformat : integralFormatOfEvidence profile resultType = .ok value.format) :
      CallablePureExpression profile (fuel + 1)
        {expression := .integer n, sourceType := sourceType, type := resultType}
  | convert (fuel : Nat) (operand : TypedCallableExpression) (sourceType resultType : CppTypeEvidence)
      (fmt : IntegralFormat) (hoperand : CallablePureExpression profile fuel operand)
      (hformat : integralFormatOfEvidence profile resultType = .ok fmt) :
      CallablePureExpression profile (fuel + 1)
        {expression := .convert operand, sourceType := sourceType, type := resultType}
  | conditional (fuel : Nat) (condition whenTrue whenFalse : TypedCallableExpression)
      (sourceType resultType : CppTypeEvidence) (hc : CallablePureExpression profile fuel condition)
      (ht : CallablePureExpression profile fuel whenTrue) (hf : CallablePureExpression profile fuel whenFalse) :
      CallablePureExpression profile (fuel + 1)
        {expression := .conditional condition whenTrue whenFalse, sourceType := sourceType, type := resultType}

theorem CallablePureExpression.derivable {profile : TargetProfile} {fuel : Nat}
    {expression : TypedCallableExpression} (fragment : CallablePureExpression profile fuel expression)
    (parameters : List CallableParameter) (arguments : List IntegralValue) (frame : IntegralObjectFrame) :
    ∃ result, CallableExpressionDerivation profile parameters fuel arguments frame expression result arguments frame := by
  induction fragment with
  | literal fuel n value st rt hs hf =>
      exact ⟨_, CallableExpressionDerivation.literal fuel arguments frame n value st rt hs hf⟩
  | convert fuel operand st rt fmt ho hf ih =>
      obtain ⟨result, dr⟩ := ih
      exact ⟨_, CallableExpressionDerivation.convert fuel arguments arguments frame frame operand st rt fmt result dr hf⟩
  | conditional fuel cond yes no st rt hc ht hf ihc iht ihf =>
      obtain ⟨conditionResult, dc⟩ := ihc
      cases conditionResult with
      | ok value =>
          by_cases hz : value.value = 0
          · obtain ⟨result, db⟩ := ihf
            refine ⟨result, CallableExpressionDerivation.conditional fuel arguments arguments arguments frame frame frame
              cond yes no st rt value result dc ?_⟩
            simpa [hz] using db
          · obtain ⟨result, db⟩ := iht
            refine ⟨result, CallableExpressionDerivation.conditional fuel arguments arguments arguments frame frame frame
              cond yes no st rt value result dc ?_⟩
            simpa [hz] using db
      | invalid reason =>
          exact ⟨_, CallableExpressionDerivation.conditionalNonvalue fuel arguments arguments frame frame
            cond yes no st rt (.invalid reason) (by intro v h; cases h) dc⟩
      | undefined reason =>
          exact ⟨_, CallableExpressionDerivation.conditionalNonvalue fuel arguments arguments frame frame
            cond yes no st rt (.undefined reason) (by intro v h; cases h) dc⟩
      | unsupported reason =>
          exact ⟨_, CallableExpressionDerivation.conditionalNonvalue fuel arguments arguments frame frame
            cond yes no st rt (.unsupported reason) (by intro v h; cases h) dc⟩

theorem CallablePureExpression.agreement {profile : TargetProfile} {fuel : Nat}
    {expression : TypedCallableExpression} (fragment : CallablePureExpression profile fuel expression)
    (parameters : List CallableParameter) (arguments : List IntegralValue) (frame : IntegralObjectFrame) :
    ∃ result, evaluateCallableExpression fuel profile parameters arguments expression = .ok (result, arguments) ∧
      evaluateCallableObjectExpression fuel profile frame expression = {frame := frame, result := .ok result} := by
  obtain ⟨result, derivation⟩ := fragment.derivable parameters arguments frame
  exact ⟨result, derivation.sound⟩

end LeanModels.Cpp
