import LeanModels.Cpp.CallableEvaluation
import LeanModels.Cpp.CallableTests

namespace LeanModels.Cpp.CallableEvaluationTests

open LeanModels.Cpp
open LeanModels.Cpp.CallableTests

-- Fuel budgets include retained source blocks; they bound depth, not executed steps.
private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩
private def short (value : Int) : IntegralValue := ⟨.signed 16, value⟩
private def unsigned (value : Int) : IntegralValue := ⟨.unsigned 32, value⟩
private def boolean (value : Int) : IntegralValue := ⟨.boolean, value⟩

private def admitFirst : Except String CallableFunction :=
  admitCallableFunction
    (probeFor (functionSource "first" [parameterRaw "0x10" "left", parameterRaw "0x11" "right"]
      (body (returnStmt "0x31" (implicitCast "0x32" (declRef "0x10" "left")))))
      [rootEvidence, functionEvidence "first" "CompoundStmt"])
    binaryTypes [] .lp64 [0]

private def admitBooleanIdentity : Except String CallableFunction :=
  admitCallableFunction identityProbe [
    typeRow "0x2" (.function (.builtin .boolean) [.builtin .boolean] false),
    typeRow "0x10" (.builtin .boolean)] [] .lp64 [0]

#guard match admitBoolCast with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [signed 7] with
      | .ok (.ok value) => value == boolean 1
      | _ => false
  | .error _ => false

#guard match admitBoolCast with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [signed 0] with
      | .ok (.ok value) => value == boolean 0
      | _ => false
  | .error _ => false

#guard match admitIf with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [] with
      | .ok (.ok value) => value == signed 7
      | _ => false
  | .error _ => false

#guard match admitWhile with
  | .ok function =>
      match evaluateCallable 12 .lp64 function [signed 0] with
      | .ok (.ok value) => value == signed 0
      | _ => false
  | .error _ => false

#guard match admitUnary with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 7] with
      | .ok (.ok value) => value == signed (-7)
      | _ => false
  | .error _ => false

#guard match admitLogical with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 7, signed 3] with
      | .ok (.ok value) => value == boolean 1
      | _ => false
  | .error _ => false

#guard match admitLogical with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 0, signed 3] with
      | .ok (.ok value) => value == boolean 0
      | _ => false
  | .error _ => false

#guard match admitWhile with
  | .ok function =>
      match evaluateCallable 12 .lp64 function [signed 7] with
      | .ok (.ok value) => value == signed 7
      | _ => false
  | .error _ => false

#guard match admitDo with
  | .ok function =>
      match evaluateCallable 12 .lp64 function [signed 0] with
      | .ok (.ok value) => value == signed 7
      | _ => false
  | .error _ => false

#guard match admitDo with
  | .ok function =>
      match evaluateCallable 12 .lp64 function [signed 1] with
      | .error .fuelExhausted => true
      | _ => false
  | .error _ => false

#guard match admitIf with
  | .ok function =>
      match function.body with
      | .block (.conditional _ whenTrue whenFalse) =>
          let zero : TypedCallableExpression := {
            expression := .integer 0, sourceType := .builtin .int, type := .builtin .int}
          let function := {function with
            body := .conditional zero whenTrue whenFalse}
          match evaluateCallable 16 .lp64 function [] with
          | .ok (.ok value) => value == signed 8
          | _ => false
      | _ => false
  | .error _ => false

#guard match admitIdentity with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [signed 17] with
      | .ok (.ok value) => value == signed 17
      | _ => false
  | .error _ => false

#guard match admitAssignment with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 4] with
      | .ok (.ok value) => value == signed 5
      | _ => false
  | .error _ => false

#guard match admitPrefixIncrement with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 4] with
      | .ok (.ok value) => value == signed 5
      | _ => false
  | .error _ => false

#guard match admitPostfixIncrement with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 4] with
      | .ok (.ok value) => value == signed 4
      | _ => false
  | .error _ => false

#guard match admitDecrement with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 4] with
      | .ok (.ok value) => value == signed 3
      | _ => false
  | .error _ => false

#guard match admitConditional with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 7] with
      | .ok (.ok value) => value == signed 7
      | _ => false
  | .error _ => false

#guard match admitComma with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 4] with
      | .ok (.ok value) => value == signed 5
      | _ => false
  | .error _ => false

#guard match admitComma with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 2147483647] with
      | .ok (.undefined .signedOverflow) => true
      | _ => false
  | .error _ => false

#guard match admitFor with
  | .ok function =>
      match evaluateCallable 64 .lp64 function [signed (-9)] with
      | .ok (.ok value) => value == signed 4
      | _ => false
  | .error _ => false

#guard match admitForBreak with
  | .ok function =>
      match evaluateCallable 64 .lp64 function [signed 0] with
      | .ok (.ok value) => value == signed 1
      | _ => false
  | .error _ => false

#guard match admitForContinue with
  | .ok function =>
      match evaluateCallable 64 .lp64 function [signed 0] with
      | .ok (.ok value) => value == signed 3
      | _ => false
  | .error _ => false

#guard match admitSwitch with
  | .ok function =>
      match evaluateCallable 64 .lp64 function [signed 0] with
      | .ok (.ok value) => value == signed 4
      | _ => false
  | .error _ => false

#guard match admitSwitch with
  | .ok function =>
      match evaluateCallable 64 .lp64 function [signed 1] with
      | .ok (.ok value) => value == signed 3
      | _ => false
  | .error _ => false

#guard match admitSwitch with
  | .ok function =>
      match evaluateCallable 64 .lp64 function [signed 2] with
      | .ok (.ok value) => value == signed 2
      | _ => false
  | .error _ => false

#guard match admitSwitch with
  | .ok function =>
      match evaluateCallable 64 .lp64 function [signed 7] with
      | .ok (.ok value) => value == signed 10
      | _ => false
  | .error _ => false

#guard match admitIdentity with
  | .ok function =>
      let condition : TypedCallableExpression := {
        expression := .integer 1, sourceType := .builtin .int, type := .builtin .int}
      let function := {function with
        body := .switch_ condition [{label := none, body := .continue_}]}
      match evaluateCallable 16 .lp64 function [signed 0] with
      | .error .continueOutsideLoop => true
      | _ => false
  | .error _ => false

#guard match admitBreak with
  | .ok function =>
      match evaluateCallable 32 .lp64 function [signed (-1)] with
      | .ok (.ok value) => value == signed 0
      | _ => false
  | .error _ => false

#guard match admitContinue with
  | .ok function =>
      match evaluateCallable 32 .lp64 function [signed 0] with
      | .ok (.ok value) => value == signed 3
      | _ => false
  | .error _ => false

#guard match admitDoBreak with
  | .ok function =>
      match evaluateCallable 32 .lp64 function [signed 0] with
      | .ok (.ok value) => value == signed 1
      | _ => false
  | .error _ => false

#guard match admitDoContinue with
  | .ok function =>
      match evaluateCallable 32 .lp64 function [signed 0] with
      | .ok (.ok value) => value == signed 3
      | _ => false
  | .error _ => false

#guard match admitLogicalEffect "&&" "bothIncrement" with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed (-1)] with
      | .ok (.ok value) => value == boolean 0
      | _ => false
  | .error _ => false

#guard match admitLogicalEffect "&&" "bothIncrement" with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 0] with
      | .ok (.ok value) => value == boolean 0
      | _ => false
  | .error _ => false

#guard match admitLogicalEffect "||" "eitherIncrement" with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 0] with
      | .ok (.ok value) => value == boolean 1
      | _ => false
  | .error _ => false

#guard match admitConditional with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 0] with
      | .ok (.ok value) => value == signed 3
      | _ => false
  | .error _ => false

#guard match admitPrefixIncrement with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 2147483647] with
      | .ok (.undefined .signedOverflow) => true
      | _ => false
  | .error _ => false

#guard match admitCompoundAssignment with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 4] with
      | .ok (.ok value) => value == signed 5
      | _ => false
  | .error _ => false

#guard match admitCompoundAssignment with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed (-1)] with
      | .ok (.ok value) => value == signed 0
      | _ => false
  | .error _ => false

#guard match admitCompoundAssignment with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed 2147483647] with
      | .ok (.undefined .signedOverflow) => true
      | _ => false
  | .error _ => false

#guard match admitAssignment with
  | .ok function =>
      match evaluateCallable 16 .lp64 function [signed (-1)] with
      | .ok (.ok value) => value == signed 0
      | _ => false
  | .error _ => false

#guard match admitIdentity with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [short 17] with
      | .ok (.ok value) => value == signed 17
      | _ => false
  | .error _ => false

#guard match admitIdentity with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [unsigned 4294967295] with
      | .ok (.ok value) => value == signed (-1)
      | _ => false
  | .error _ => false

#guard match admitIdentity with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [boolean 1] with
      | .ok (.ok value) => value == signed 1
      | _ => false
  | .error _ => false

#guard match admitIdentity with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [⟨.signed 16, 40000⟩] with
      | .ok (.invalid .outOfRange) => true
      | _ => false
  | .error _ => false

#guard match admitFirst with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [short 17, unsigned 4294967295] with
      | .ok (.ok value) => value == signed 17
      | _ => false
  | .error _ => false

#guard match admitFirst with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [signed 17, ⟨.unsigned 0, 0⟩] with
      | .ok (.invalid .zeroWidth) => true
      | _ => false
  | .error _ => false

#guard match admitFirst with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [signed 17, ⟨.signed 16, 40000⟩] with
      | .ok (.invalid .outOfRange) => true
      | _ => false
  | .error _ => false

#guard match admitBooleanIdentity with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [signed (-7)] with
      | .ok (.ok value) => value == boolean 1
      | _ => false
  | .error _ => false

#guard match admitBooleanIdentity with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [signed 0] with
      | .ok (.ok value) => value == boolean 0
      | _ => false
  | .error _ => false

#guard match admitLiteral with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [] with
      | .ok (.ok value) => value == signed 7
      | _ => false
  | .error _ => false

#guard match admitBinary with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [signed 4, signed 9] with
      | .ok (.ok value) => value == signed 13
      | _ => false
  | .error _ => false

#guard match admitBinary with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [short 17, unsigned 4294967295] with
      | .ok (.ok value) => value == signed 16
      | _ => false
  | .error _ => false

#guard match admitIdentity with
  | .ok function =>
      match evaluateCallable 4 {TargetProfile.lp64 with intWidth := 16} function [signed 65535] with
      | .ok (.ok value) => value == ⟨.signed 16, -1⟩
      | _ => false
  | .error _ => false

#guard match admitBinary with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [signed 2147483647, signed 1] with
      | .ok (.undefined .signedOverflow) => true
      | _ => false
  | .error _ => false

#guard match admitBinary with
  | .ok function =>
      match evaluateCallable 0 .lp64 function [signed 1, signed 2] with
      | .error .fuelExhausted => true
      | _ => false
  | .error _ => false

#guard match admitIdentity with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [] with
      | .error .arityMismatch => true
      | _ => false
  | .error _ => false

#guard match admitIdentity with
  | .ok function =>
      match evaluateCallable 4 {TargetProfile.lp64 with intWidth := 8} function [signed 1] with
      | .error .invalidProfile => true
      | _ => false
  | .error _ => false

-- These overflow controls are model checks, never defined C++ oracle executions.
private def one : TypedCallableExpression := {
  expression := .integer 1, sourceType := intType, type := intType}
private def increment : TypedCallableExpression := {
  expression := .increment "++" false {value := "0x10"}, sourceType := intType, type := intType}

private def checkFor (condition : TypedCallableExpression) (step body : CallableStatement)
    (expected : IntegralResult IntegralValue) : Bool :=
  match admitIdentity with
  | .ok function =>
      let function := {function with body := .block (.sequence
        (.forLoop .skip condition step (.block body)) (.return_ (typedParameter "0x10")))}
      match evaluateCallable 64 .lp64 function [signed 2147483647] with
      | .ok result => result == expected
      | _ => false
  | .error _ => false

-- Return and break skip the overflowing step, including through block boundaries.
#guard checkFor one (.expression increment) (.return_ one) (.ok (signed 1))
#guard checkFor one (.expression increment) .break_ (.ok (signed 2147483647))
-- Continue reaches that same step; a failed condition/body never reaches a return.
#guard checkFor one (.expression increment) .continue_ (.undefined .signedOverflow)
#guard checkFor increment .skip (.return_ one) (.undefined .signedOverflow)
#guard checkFor one (.return_ one) (.expression increment) (.undefined .signedOverflow)
-- A failed step stops iteration, and finite fuel still refuses an unending for.
#guard checkFor one (.expression increment) .skip (.undefined .signedOverflow)
#guard match admitIdentity with
  | .ok function =>
      match evaluateCallable 8 .lp64 {function with body := .forLoop .skip one .skip .skip}
          [signed 0] with
      | .error .fuelExhausted => true
      | _ => false
  | .error _ => false

-- Typed literal formats are observable even without a surrounding conversion.
private def checkTypedLiteral (type : CppTypeEvidence) (literal : Nat)
    (expected : IntegralResult IntegralValue) : Bool :=
  match admitLiteral with
  | .ok function =>
      let function := {function with
        signature := {function.signature with result := type}
        body := .return_ {expression := .integer literal, sourceType := type, type}}
      (evaluateCallable 4 .lp64 function []).toOption == some expected
  | .error _ => false

#guard checkTypedLiteral (.builtin .boolean) 1 (.ok (boolean 1))
#guard checkTypedLiteral (.builtin .unsignedInt) 1 (.ok (unsigned 1))
#guard checkTypedLiteral (.builtin .long) 4294967296 (.ok ⟨.signed 64, 4294967296⟩)
#guard checkTypedLiteral (.builtin .unsignedLongLong) 18446744073709551615
  (.ok ⟨.unsigned 64, 18446744073709551615⟩)
#guard checkTypedLiteral (.builtin .int) 4294967296 (.invalid .outOfRange)

end LeanModels.Cpp.CallableEvaluationTests
