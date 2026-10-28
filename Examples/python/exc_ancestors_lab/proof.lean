import LeanModels.Python.Surface

namespace Examples.python.exc_ancestors_lab.proof

open LeanModels LeanModels.Python

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

load_program exc_ancestors_lab from "Examples/python/exc_ancestors_lab/exc_ancestors_lab.json"

private theorem floorDiv_ne_bitAnd :
    (BinOp.floorDiv == BinOp.bitAnd) = false := by decide

private theorem len_ne_lenMult :
    ("len" == lenMultBuiltinName) = false := by decide

private theorem str_ne_fstring : ("str" == fstringFormatBuiltinName) = false := by decide
private theorem str_ne_starArg : ("str" == starArgBuiltinName) = false := by decide
private theorem str_ne_starTuple : ("str" == starTupleBuiltinName) = false := by decide
private theorem str_ne_starList : ("str" == starListBuiltinName) = false := by decide

theorem caught_arithmetic_identity_total (value : PyInt) :
    exc_ancestors_lab.caught_arithmetic_identity(value) ==> value := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [exc_ancestors_lab, excHandlerNames, excHandlerTuple,
    excHandlerAdmitted, excHandlerMatches, floorDiv_ne_bitAnd,
    len_ne_lenMult, str_ne_fstring, str_ne_starArg, str_ne_starTuple,
    str_ne_starList, lenMultBuiltinName, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFree, Stmt.heapFreeList, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, hasUnboundLocal,
    unboundLocalMarker, isLoweredBuiltinName, isPyBuiltinName,
    flattenStarRun, flattenStarCallArgs, userExcCatches, classAtExc,
    builtinExcNameCatches, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]

#print axioms caught_arithmetic_identity_total

end Examples.python.exc_ancestors_lab.proof
