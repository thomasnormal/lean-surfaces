import Examples.cpp.tinyxml2.IsUTF8Continuation

namespace Examples.cpp.tinyxml2.IsUTF8Continuation

open LeanModels.Cpp

/-- The public observation also records failure: every error, undefined result,
unsupported result and non-boolean result is `none`, never a vacuous success. -/
def observed (input : Int) : Option Int :=
  match evaluateCallable 32 .lp64 function [⟨.signed 8, input⟩] with
  | .ok (.ok ⟨.boolean, value⟩) => some value
  | _ => none

-- Kernel decide is used because the pinned source's complete char domain has
-- exactly 256 inputs. This checks the generated real body, not a native oracle.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem allBytes :
    (List.range 256).all (fun encoded =>
      observed (Int.ofNat encoded - 128) == some (if encoded < 128 then 1 else 0)) = true := by
  decide

/-- TinyXML-2's named predicate tests the high bit. On this signed-char ABI,
every negative char returns true and every nonnegative char returns false. -/
theorem observed_high_bit (input : Int) (lower : -128 ≤ input) (upper : input < 128) :
    observed input = some (if input < 0 then 1 else 0) := by
  let encoded := (input + 128).toNat
  have bound : encoded < 256 := by dsimp [encoded]; omega
  have check := (List.all_eq_true.mp allBytes) encoded (List.mem_range.mpr bound)
  have equation : Int.ofNat encoded - 128 = input := by dsimp [encoded]; omega
  have sign : encoded < 128 ↔ input < 0 := by dsimp [encoded]; omega
  have check' : observed (Int.ofNat encoded - 128) =
      some (if encoded < 128 then 1 else 0) := by simpa using check
  simpa only [equation, sign] using check'

private theorem success_of_observed
    (result : Except CallableEvaluationError (IntegralResult IntegralValue))
    (expected : Int)
    (h : (match result with
      | .ok (.ok ⟨.boolean, value⟩) => some value
      | _ => none) = some expected) :
    result = .ok (.ok ⟨.boolean, expected⟩) := by
  cases result with
  | error reason => cases h
  | ok result =>
      cases result with
      | invalid reason => cases h
      | undefined reason => cases h
      | unsupported reason => cases h
      | ok value =>
          rcases value with ⟨format, value⟩
          cases format <;> simp_all

/-- A total successful execution theorem for every valid char in the pinned
LP64 profile, including the actual boolean result constructor. -/
theorem returns_high_bit (input : Int) (lower : -128 ≤ input) (upper : input < 128) :
    evaluateCallable 32 .lp64 function [⟨.signed 8, input⟩] =
      .ok (.ok ⟨.boolean, if input < 0 then 1 else 0⟩) :=
  success_of_observed _ _ (observed_high_bit input lower upper)

example : function.occurrence.name = some "IsUTF8Continuation" := rfl
example : function.occurrence.kind = "CXXMethodDecl" := rfl

#print axioms allBytes
#print axioms observed_high_bit
#print axioms returns_high_bit

end Examples.cpp.tinyxml2.IsUTF8Continuation
