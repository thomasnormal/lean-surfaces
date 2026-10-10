import LeanModels.Python.Surface

namespace Examples.python.exc_handlers_lab.proof

open LeanModels LeanModels.Python

load_program exc_handlers_lab from "Examples/python/exc_handlers_lab/exc_handlers_lab.json"

theorem caught_type_identity_total (value : PyInt) :
    exc_handlers_lab.caught_type_identity(value) ==> value := by
  py_prove [exc_handlers_lab]

#print axioms caught_type_identity_total

end Examples.python.exc_handlers_lab.proof
