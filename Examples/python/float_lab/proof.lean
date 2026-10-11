import LeanModels.Python.Surface

namespace Examples.python.float_lab.proof

open LeanModels LeanModels.Python

load_program float_lab from "Examples/python/float_lab/float_lab.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem tenth :
    float_lab.tenth() ==> Float64.ofBits 0x3fb999999999999a := by
  exact ⟨32, rfl⟩

theorem integer_true :
    float_lab.integer_true() ==> Float64.ofBits 0x4004000000000000 := by
  exact ⟨32, rfl⟩

theorem default_passthrough (value : PyFloat) :
    float_lab.default(value) ==> value := by
  exact ⟨32, rfl⟩

theorem addition :
    float_lab.addition() ==> Float64.ofBits 0x4008000000000000 := by
  exact ⟨32, rfl⟩

private theorem add_quarter :
    Float64.arithmetic .add (Float64.ofBits 0x3fe0000000000000)
      (Float64.ofBits 0x3fd0000000000000) = .ok (Float64.ofBits 0x3fe8000000000000) := rfl

private theorem subtract_eighth :
    Float64.arithmetic .sub (Float64.ofBits 0x3fe8000000000000)
      (Float64.ofBits 0x3fc0000000000000) = .ok (Float64.ofBits 0x3fe4000000000000) := rfl

private theorem multiply_negative_two :
    Float64.arithmetic .mult (Float64.ofBits 0x3fe4000000000000)
      (Float64.ofBits 0xc000000000000000) = .ok (Float64.ofBits 0xbff4000000000000) := rfl

theorem augmented :
    float_lab.augmented() ==> Float64.ofBits 0xbff4000000000000 := by
  have addStep : Float64.arithmetic .add ⟨0x3fe0000000000000⟩ ⟨0x3fd0000000000000⟩ =
      .ok ⟨0x3fe8000000000000⟩ := add_quarter
  have subtractStep : Float64.arithmetic .sub ⟨0x3fe8000000000000⟩ ⟨0x3fc0000000000000⟩ =
      .ok ⟨0x3fe4000000000000⟩ := subtract_eighth
  have multiplyStep : Float64.arithmetic .mult ⟨0x3fe4000000000000⟩ ⟨0xc000000000000000⟩ =
      .ok ⟨0xbff4000000000000⟩ := multiply_negative_two
  have negateStep : (⟨0x4000000000000000⟩ : Float64).neg = ⟨0xc000000000000000⟩ := rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [float_lab, evalFloatArithmetic, floatNumber,
    addStep, subtractStep, multiplyStep, negateStep]
  rfl

theorem mixed_rounding :
    float_lab.mixed_rounding() ==> Float64.ofBits 0x4340000000000000 := by
  exact ⟨32, rfl⟩

theorem cancel (value : PyFloat) (finite : value.exponent ≠ 2047) :
    float_lab.cancel(value) ==> Float64.ofBits 0 := by
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [float_lab, evalFloatArithmetic, floatNumber, Float64.arithmetic_sub_self, finite]

#print axioms tenth
#print axioms integer_true
#print axioms default_passthrough
#print axioms addition
#print axioms augmented
#print axioms mixed_rounding
#print axioms cancel
#print axioms add_quarter
#print axioms subtract_eighth
#print axioms multiply_negative_two

end Examples.python.float_lab.proof
