import LeanModels.Python.Surface

namespace Examples.python.builtin_raise_lab.proof
open LeanModels LeanModels.Python
load_program builtin_raise_lab from "Examples/python/builtin_raise_lab/builtin_raise_lab.json"

theorem catch_value_error_total (value : PyInt) :
    builtin_raise_lab.catch_ValueError(value) ==> value := by
  exact CallsTo.intro 64 (by rfl)

#print axioms catch_value_error_total
end Examples.python.builtin_raise_lab.proof
