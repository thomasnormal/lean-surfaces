import LeanModels.Python.Surface

namespace Examples.python.ellipsis_lab.proof

open LeanModels LeanModels.Python

load_program ellipsis_lab from "Examples/python/ellipsis_lab/ellipsis_lab.json"

set_option maxRecDepth 8192

theorem branch_singleton (value : PyBool) :
    ellipsis_lab.branch(value) ==> (if value then Val.ellipsis else Val.none) := by
  refine ⟨32, ?_⟩
  cases value <;>
    py_simp [callFunction, callIn, ellipsis_lab, pythonTopCallDepth,
      pythonRecursionLimit, Run.finishCallAt, Run.leaveCallDepth,
      Run.toPublic, Run.toPublic_ok, RVal.freezeB]

theorem integer_identity (value : PyInt) :
    ellipsis_lab.identity(value) ==>
      (Val.tuple #[.bool false, .bool true, .bool false, .bool true]) := by
  py_prove [ellipsis_lab, RVal.isEllipsis, pythonTopCallDepth,
    pythonRecursionLimit, Run.finishCallAt, Run.leaveCallDepth, Run.toPublic,
    Run.toPublic_ok, RVal.freezeB]

theorem notimplemented_builtin :
    ellipsis_lab.notimplemented_builtin() ==> Val.notImplemented := by
  py_prove [ellipsis_lab, RVal.isNotImplemented, hasUnboundLocal,
    starListBuiltinName, starTupleBuiltinName, Run.toPublic, RVal.freezeB,
    unboundLocalMarker, isPyBuiltinName, isLoweredBuiltinName,
    smallIntIdentity, Env.lookup, pythonTopCallDepth, pythonRecursionLimit,
    Run.finishCallAt, Run.leaveCallDepth, Run.toPublic_ok]

#print axioms branch_singleton
#print axioms integer_identity
#print axioms notimplemented_builtin

end Examples.python.ellipsis_lab.proof
