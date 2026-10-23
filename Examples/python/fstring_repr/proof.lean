import LeanModels

namespace Examples.python.fstring_repr.proof

open LeanModels LeanModels.Python

load_program fstring_repr from "Examples/python/fstring_repr/fstring_repr.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 4300

theorem boolean_field (value : PyBool) :
    fstring_repr.repr_field(value) ==> ("[" ++ (if value then "True" else "False") ++ "]") := by
  py_prove [fstring_repr, reprVal]

theorem integer_field (value : PyInt) (valueBound : value.natAbs < 10 ^ 4300) :
    fstring_repr.repr_field(value) ==> ("[" ++ toString value ++ "]") := by
  have rendered : intDecimal value = some (toString value) := by
    unfold intDecimal
    exact if_pos valueBound
  py_prove [fstring_repr, reprVal, rendered]

theorem unicode_str_field (value : PyStr) :
    fstring_repr.str_field(value) ==> ("[" ++ value ++ "]") := by
  py_prove [fstring_repr]

#print axioms boolean_field
#print axioms integer_field
#print axioms unicode_str_field

end Examples.python.fstring_repr.proof
