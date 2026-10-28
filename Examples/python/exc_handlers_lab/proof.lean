import LeanModels.Python.Surface

namespace Examples.python.exc_handlers_lab.proof

open LeanModels LeanModels.Python

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

load_program exc_handlers_lab from "Examples/python/exc_handlers_lab/exc_handlers_lab.json"

private theorem floorDiv_ne_bitAnd :
    (BinOp.floorDiv == BinOp.bitAnd) = false := by
  decide

private theorem len_ne_lenMult :
    ("len" == lenMultBuiltinName) = false := by
  decide

theorem caught_type_identity_total (value : PyInt) :
    exc_handlers_lab.caught_type_identity(value) ==> value := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [exc_handlers_lab, excHandlerNames, excHandlerTuple,
    excHandlerAdmitted, excHandlerMatches, floorDiv_ne_bitAnd,
    len_ne_lenMult, lenMultBuiltinName, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFree, Stmt.heapFreeList, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, hasUnboundLocal,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun, flattenStarCallArgs,
    userExcCatches, classAtExc, builtinExcNameCatches, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB]
  rfl

theorem tuple_handler :
    exc_handlers_lab.tuple_handler() ==> (13 : PyInt) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [exc_handlers_lab, excHandlerNames, excHandlerTuple,
    excHandlerAdmitted, excHandlerMatches, floorDiv_ne_bitAnd,
    len_ne_lenMult, lenMultBuiltinName, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFree, Stmt.heapFreeList, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, hasUnboundLocal,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun, flattenStarCallArgs,
    userExcCatches, classAtExc, builtinExcNameCatches, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB]

#print axioms caught_type_identity_total

end Examples.python.exc_handlers_lab.proof
