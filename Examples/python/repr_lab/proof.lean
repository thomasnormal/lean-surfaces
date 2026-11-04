import LeanModels.Python.Surface

namespace Examples.python.repr_lab.proof

open LeanModels LeanModels.Python

set_option maxHeartbeats 2000000

load_program repr_lab from "Examples/python/repr_lab/repr_lab.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 4300

private theorem repr_ne_fstring : ("repr" == fstringFormatBuiltinName) = false := by decide
private theorem repr_ne_starArg : ("repr" == starArgBuiltinName) = false := by decide
private theorem repr_ne_starTuple : ("repr" == starTupleBuiltinName) = false := by decide
private theorem repr_ne_starList : ("repr" == starListBuiltinName) = false := by decide

theorem boolean_repr (value : PyBool) :
    repr_lab.of(value) ==> (if value then "True" else "False") := by
  intros
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [repr_lab, reprVal, lenMultBuiltinName, decimalOverflowValH,
    decimalOverflowImmediate]
  all_goals simp only [funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList,
    Stmt.heapFree, Expr.heapFreeList, Expr.heapFree]
  all_goals simp [repr_ne_fstring, repr_ne_starArg, repr_ne_starTuple,
    repr_ne_starList, starArgBuiltinName, starListBuiltinName, starTupleBuiltinName,
    fstringFormatBuiltinName, lenMultBuiltinName, hasUnboundLocal,
    unboundLocalMarker, Env.lookup]
  all_goals py_simp [reprVal, reprArgsH, reprArgs, reprVal, printOne,
    flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic,
    RVal.freezeB]
  all_goals simp [decimalOverflowValH, decimalOverflowImmediate, Run.toPublic,
    Run.bind, Run.liftRes, RVal.freezeB]

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
  all_goals simp only [funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList,
    Stmt.heapFree, Expr.heapFreeList, Expr.heapFree]
  all_goals simp [repr_ne_fstring, repr_ne_starArg, repr_ne_starTuple,
    repr_ne_starList, starArgBuiltinName, starListBuiltinName, starTupleBuiltinName,
    fstringFormatBuiltinName, lenMultBuiltinName, hasUnboundLocal,
    unboundLocalMarker, Env.lookup]
  all_goals py_simp [reprVal, reprArgsH, reprArgs, reprVal, printOne,
    flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic,
    RVal.freezeB]
  all_goals simp [decimalOverflowValH, decimalOverflowImmediate, rendered,
    Run.toPublic, Run.bind, Run.liftRes, RVal.freezeB]

#print axioms boolean_repr
#print axioms integer_repr

end Examples.python.repr_lab.proof
