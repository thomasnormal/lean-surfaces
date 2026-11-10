import LeanModels.Python

namespace Examples.python.sum_order_lab.proof

open LeanModels LeanModels.Python

load_program sum_order_lab from "Examples/python/sum_order_lab/sum_order_lab.json"

attribute [local implicit_reducible] sum_order_lab

private theorem initial_world :
    initWorld sum_order_lab = (⟨#[], [], [], [], 0⟩ : World) := by
  rfl

private theorem values_not_genexp : "values".startsWith genExpPrefix = false := by
  decide

theorem int_before_string_start (value : PyInt) (start : PyStr) :
    sum_order_lab.rejected_start(value, start) ==>!
      (.typeError "'int' object is not iterable") := by
  exact ⟨64, rfl⟩

theorem int_before_bytes_start (value : PyInt) (start : PyBytes) :
    sum_order_lab.rejected_start(value, start) ==>!
      (.typeError "'int' object is not iterable") := by
  exact ⟨64, rfl⟩

theorem string_start_preserves_generator (start : PyStr) :
    sum_order_lab.generator_untouched(start) ==> (7 : PyInt) := by
  refine ⟨11, ?_⟩
  unfold callFunction
  rw [initial_world]
  rw [callIn.eq_2]
  py_simp [sum_order_lab, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFree, Stmt.heapFreeList, Expr.heapFree, hasUnboundLocal,
    unboundLocalMarker, flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes,
    genExpCreationRun, values_not_genexp]
  simp only [pythonTopCallDepth, pythonRecursionLimit,
    show (0 : Nat) ≠ 1000 + 1 from by decide, if_false, starArgBuiltinName,
    typeErrorTargetList, typeErrorTarget, stmtUnboundLocalNamesList,
    stmtUnboundLocalNames, Bool.false_or, Bool.or_false, List.append_nil,
    List.nil_append, List.foldl_nil, ↓reduceIte]
  simp only [show "values" ≠ "<star-arg>" from by decide,
    show ("cursor" == "TypeError") = false from by decide,
    Bool.false_eq_true, if_false]
  py_simp [sum_order_lab, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFree, Stmt.heapFreeList, Expr.heapFree, hasUnboundLocal,
    unboundLocalMarker, flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes]
  rw [callIn.eq_2]
  py_simp [sum_order_lab, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFree, Stmt.heapFreeList, Expr.heapFree, hasUnboundLocal,
    unboundLocalMarker, flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes,
    genExpCreationRun, values_not_genexp]
  py_simp [excHandlerBare, excHandlerTuple, excHandlerPrimary, excHandlerAdmitted,
    excHandlerMatches, fstringFormatBuiltinName, lenMultBuiltinName,
    starArgBuiltinName, starListBuiltinName, starTupleBuiltinName,
    isLoweredBuiltinName, isPyBuiltinName, hasUnboundLocal, unboundLocalMarker,
    flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes, sumRejectedStart]
  rw [stepIter.eq_2]
  py_simp [nativeIteratorName]
  rw [execGen.eq_4]
  py_simp [genPlan, Stmt.hasYield, Run.bindE, Run.toWorld, Run.withLocals,
    Run.leaveCallDepth]

theorem bytes_start_preserves_generator (start : PyBytes) :
    sum_order_lab.generator_untouched(start) ==> (7 : PyInt) := by
  refine ⟨11, ?_⟩
  unfold callFunction
  rw [initial_world]
  rw [callIn.eq_2]
  py_simp [sum_order_lab, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFree, Stmt.heapFreeList, Expr.heapFree, hasUnboundLocal,
    unboundLocalMarker, flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes,
    genExpCreationRun, values_not_genexp]
  simp only [pythonTopCallDepth, pythonRecursionLimit,
    show (0 : Nat) ≠ 1000 + 1 from by decide, if_false, starArgBuiltinName,
    typeErrorTargetList, typeErrorTarget, stmtUnboundLocalNamesList,
    stmtUnboundLocalNames, Bool.false_or, Bool.or_false, List.append_nil,
    List.nil_append, List.foldl_nil, ↓reduceIte]
  simp only [show "values" ≠ "<star-arg>" from by decide,
    show ("cursor" == "TypeError") = false from by decide,
    Bool.false_eq_true, if_false]
  py_simp [sum_order_lab, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFree, Stmt.heapFreeList, Expr.heapFree, hasUnboundLocal,
    unboundLocalMarker, flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes]
  rw [callIn.eq_2]
  py_simp [sum_order_lab, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFree, Stmt.heapFreeList, Expr.heapFree, hasUnboundLocal,
    unboundLocalMarker, flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes,
    genExpCreationRun, values_not_genexp]
  py_simp [excHandlerBare, excHandlerTuple, excHandlerPrimary, excHandlerAdmitted,
    excHandlerMatches, fstringFormatBuiltinName, lenMultBuiltinName,
    starArgBuiltinName, starListBuiltinName, starTupleBuiltinName,
    isLoweredBuiltinName, isPyBuiltinName, hasUnboundLocal, unboundLocalMarker,
    flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes, sumRejectedStart]
  rw [stepIter.eq_2]
  py_simp [nativeIteratorName]
  rw [execGen.eq_4]
  py_simp [genPlan, Stmt.hasYield, Run.bindE, Run.toWorld, Run.withLocals,
    Run.leaveCallDepth]

#print axioms int_before_string_start
#print axioms int_before_bytes_start
#print axioms string_start_preserves_generator
#print axioms bytes_start_preserves_generator

end Examples.python.sum_order_lab.proof
