import LeanModels.Python.Surface

namespace Examples.python.bool_lab.proof

open LeanModels LeanModels.Python

load_program bool_lab from "Examples/python/bool_lab/bool_lab.json"

theorem integer_truth (value : PyInt) :
    bool_lab.of(value) ==> (value != 0) := by
  py_prove [bool_lab]

theorem boolean_identity (value : PyBool) :
    bool_lab.of(value) ==> value := by
  py_prove [bool_lab]

#print axioms integer_truth
#print axioms boolean_identity

end Examples.python.bool_lab.proof
