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

#print axioms tenth
#print axioms integer_true
#print axioms default_passthrough

end Examples.python.float_lab.proof
