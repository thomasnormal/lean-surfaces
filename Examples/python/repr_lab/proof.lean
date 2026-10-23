import LeanModels.Python.Surface

namespace Examples.python.repr_lab.proof

open LeanModels LeanModels.Python

load_program repr_lab from "Examples/python/repr_lab/repr_lab.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

theorem boolean_repr (value : PyBool) :
    repr_lab.of(value) ==> (if value then "True" else "False") := by
  py_prove [repr_lab, reprVal]

theorem integer_repr (value : PyInt) (valueBound : value.natAbs < 10 ^ 1024) :
    repr_lab.of(value) ==> toString value := by
  have rendered : intDecimal value = some (toString value) := by
    unfold intDecimal
    exact if_pos valueBound
  py_prove [repr_lab, reprVal, rendered]

#print axioms boolean_repr
#print axioms integer_repr

end Examples.python.repr_lab.proof
