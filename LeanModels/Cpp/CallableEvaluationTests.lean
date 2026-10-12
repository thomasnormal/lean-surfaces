import LeanModels.Cpp.CallableEvaluation
import LeanModels.Cpp.CallableTests

namespace LeanModels.Cpp.CallableEvaluationTests

open LeanModels.Cpp
open LeanModels.Cpp.CallableTests

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

#guard match admitIf with
  | .ok function =>
      match evaluateCallable 8 .lp64 function [] with
      | .ok (.ok value) => value == signed 7
      | _ => false
  | .error _ => false

#guard match admitIf with
  | .ok function =>
      match function.body with
      | .conditional _ whenTrue whenFalse =>
          let zero : TypedCallableExpression := {
            expression := .integer 0, sourceType := .builtin .int, type := .builtin .int}
          let function := {function with
            body := .conditional zero whenTrue whenFalse}
          match evaluateCallable 8 .lp64 function [] with
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
      match evaluateCallable 2 .lp64 function [] with
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

end LeanModels.Cpp.CallableEvaluationTests
