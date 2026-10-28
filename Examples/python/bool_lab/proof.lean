import LeanModels.Python.Surface

namespace Examples.python.bool_lab.proof

open LeanModels LeanModels.Python

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

load_program bool_lab from "Examples/python/bool_lab/bool_lab.json"

private theorem bool_ne_fstring : ("bool" == fstringFormatBuiltinName) = false := by decide
private theorem bool_ne_lenMult : ("bool" == lenMultBuiltinName) = false := by decide
private theorem bool_ne_starArg : ("bool" == starArgBuiltinName) = false := by decide
private theorem bool_ne_starTuple : ("bool" == starTupleBuiltinName) = false := by decide
private theorem bool_ne_starList : ("bool" == starListBuiltinName) = false := by decide

theorem integer_truth (value : PyInt) :
    bool_lab.of(value) ==> (value != 0) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [bool_lab, bool_ne_fstring, bool_ne_lenMult, bool_ne_starArg,
    bool_ne_starTuple, bool_ne_starList, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFree, Stmt.heapFreeList, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, hasUnboundLocal,
    unboundLocalMarker, isLoweredBuiltinName, isPyBuiltinName,
    flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB]


theorem boolean_identity (value : PyBool) :
    bool_lab.of(value) ==> value := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [bool_lab, bool_ne_fstring, bool_ne_lenMult, bool_ne_starArg,
    bool_ne_starTuple, bool_ne_starList, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFree, Stmt.heapFreeList, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, hasUnboundLocal,
    unboundLocalMarker, isLoweredBuiltinName, isPyBuiltinName,
    flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB]


#print axioms integer_truth
#print axioms boolean_identity

end Examples.python.bool_lab.proof
