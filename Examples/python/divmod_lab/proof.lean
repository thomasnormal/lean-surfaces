import LeanModels.Python.Surface

namespace Examples.python.divmod_lab.proof

open LeanModels LeanModels.Python

load_program divmod_lab from "Examples/python/divmod_lab/divmod_lab.json"

theorem by_one_total (value : PyInt) :
    divmod_lab.by_one(value) ==> (Val.tuple #[.int value, .int 0]) := by
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [divmod_lab, divmodArgs, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    topLevelDefFree, Stmt.defFreeList, Stmt.defFree, starArgBuiltinName,
    starListBuiltinName, starTupleBuiltinName, fstringFormatBuiltinName,
    lenMultBuiltinName, hasUnboundLocal, unboundLocalMarker,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Env.lookup, lookupG, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB]

#print axioms by_one_total

end Examples.python.divmod_lab.proof
