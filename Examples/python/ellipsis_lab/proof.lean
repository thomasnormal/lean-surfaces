import LeanModels.Python.Surface

namespace Examples.python.ellipsis_lab.proof

open LeanModels LeanModels.Python

load_program ellipsis_lab from "Examples/python/ellipsis_lab/ellipsis_lab.json"

set_option maxRecDepth 8192

theorem branch_singleton (value : PyBool) :
    ellipsis_lab.branch(value) ==> (if value then Val.ellipsis else Val.none) := by
  py_prove [ellipsis_lab]

theorem integer_identity (value : PyInt) :
    ellipsis_lab.identity(value) ==>
      (Val.tuple #[.bool false, .bool true, .bool false, .bool true]) := by
  py_prove [ellipsis_lab, RVal.isEllipsis]

#print axioms branch_singleton
#print axioms integer_identity

end Examples.python.ellipsis_lab.proof
