import LeanModels.Python.Surface

namespace Examples.python.exc_ancestors_lab.proof

open LeanModels LeanModels.Python

load_program exc_ancestors_lab from "Examples/python/exc_ancestors_lab/exc_ancestors_lab.json"

theorem caught_arithmetic_identity_total (value : PyInt) :
    exc_ancestors_lab.caught_arithmetic_identity(value) ==> value := by
  py_prove [exc_ancestors_lab]

#print axioms caught_arithmetic_identity_total

end Examples.python.exc_ancestors_lab.proof
