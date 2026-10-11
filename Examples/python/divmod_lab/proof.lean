import LeanModels.Python.Surface
import LeanModels.Python.Float64Tests

namespace Examples.python.divmod_lab.proof

open LeanModels LeanModels.Python

load_program divmod_lab from "Examples/python/divmod_lab/divmod_lab.json"

theorem by_one_total (value : PyInt) :
    divmod_lab.by_one(value) ==> (Val.tuple #[.int value, .int 0]) := by
  py_prove [divmod_lab]

#print axioms by_one_total

theorem float_pair_tenth :
    divmod_lab.pair(Float64.ofBits 0x3ff0000000000000,
      Float64.ofBits 0x3fb999999999999a) ==>
      (Float64.ofBits 0x4022000000000000, Float64.ofBits 0x3fb9999999999996) := by
  have floorStep : Float64.floorRem ⟨0x3ff0000000000000⟩ ⟨0x3fb999999999999a⟩ =
      .ok (⟨0x4022000000000000⟩, ⟨0x3fb9999999999996⟩) :=
    Float64.Tests.floor_remainder_tenth
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [divmod_lab, divmodArgs, evalFloatDivmod, floatNumber, Float64.ofBits, floorStep]
  rfl

#print axioms float_pair_tenth

end Examples.python.divmod_lab.proof
