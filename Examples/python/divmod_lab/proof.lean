import LeanModels.Python.Surface

namespace Examples.python.divmod_lab.proof

open LeanModels LeanModels.Python

load_program divmod_lab from "Examples/python/divmod_lab/divmod_lab.json"

theorem by_one_total (value : PyInt) :
    divmod_lab.by_one(value) ==> (Val.tuple #[.int value, .int 0]) := by
  py_prove [divmod_lab]

#print axioms by_one_total

end Examples.python.divmod_lab.proof
