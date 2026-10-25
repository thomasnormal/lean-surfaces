import LeanModels.Python.Surface

namespace Examples.python.repr_lab.proof

open LeanModels LeanModels.Python

load_program repr_lab from "Examples/python/repr_lab/repr_lab.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 4300

theorem boolean_repr (value : PyBool) :
    repr_lab.of(value) ==> (if value then "True" else "False") := by
  intros
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [repr_lab, reprVal, lenMultBuiltinName, decimalOverflowValH]

theorem integer_repr (value : PyInt) (valueBound : value.natAbs < 10 ^ 4300) :
    repr_lab.of(value) ==> toString value := by
  have rendered : intDecimal value = some (toString value) := by
    unfold intDecimal
    exact if_pos valueBound
  intros
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [repr_lab, reprVal, lenMultBuiltinName, decimalOverflowValH,
    decimalOverflowImmediate, rendered]

#print axioms boolean_repr
#print axioms integer_repr

end Examples.python.repr_lab.proof
