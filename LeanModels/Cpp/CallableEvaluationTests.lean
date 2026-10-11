import LeanModels.Cpp.CallableEvaluation
import LeanModels.Cpp.CallableTests

namespace LeanModels.Cpp.CallableEvaluationTests

open LeanModels.Cpp
open LeanModels.Cpp.CallableTests

private def signed (value : Int) : IntegralValue := ⟨.signed 32, value⟩

#guard match admitIdentity with
  | .ok function =>
      match evaluateCallable 4 .lp64 function [signed 17] with
      | .ok (.ok value) => value == signed 17
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
