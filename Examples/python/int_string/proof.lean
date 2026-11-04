import LeanModels.Python.Surface
import LeanModels.Python.VCTactic
import LeanModels.Python.Delab

namespace Examples.python.int_string.proof

open LeanModels LeanModels.Python

load_program int_string from "Examples/python/int_string/int_string.json"

private theorem grouped_decimal : intOfStr "1_024" = .ok (.int 1024) := by
  rfl

private theorem signed_decimal : intOfStr " \u000b\u000c-2_048\r\n" = .ok (.int (-2048)) := by
  rfl

private theorem add_ne_bitAnd : (BinOp.add == BinOp.bitAnd) = false := by
  decide

theorem grouped_offset_total (offset : PyInt) :
    int_string.grouped_offset(offset) ==> 1024 + offset := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [int_string, lenMultBuiltinName, intCastArgs, intCastVal, intCastBase,
    grouped_decimal, add_ne_bitAnd, evalBinOpH, PyVCGen.binOpBeqBitAnd,
    PyVCGen.binOpBeqMult, setLikeRefH, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, starArgBuiltinName,
    starListBuiltinName, starTupleBuiltinName, fstringFormatBuiltinName,
    flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic,
    RVal.freezeB]

theorem signed_adjustment_total (offset : PyInt) :
    int_string.signed_adjustment(offset) ==> offset - 2048 := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [int_string, lenMultBuiltinName, intCastArgs, intCastVal, intCastBase,
    signed_decimal, add_ne_bitAnd, evalBinOpH, PyVCGen.binOpBeqBitAnd,
    PyVCGen.binOpBeqMult, setLikeRefH, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, starArgBuiltinName,
    starListBuiltinName, starTupleBuiltinName, fstringFormatBuiltinName,
    flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic,
    RVal.freezeB]
  omega

private theorem hexadecimal :
    intCastBase (.str "0x_fF") (.int 0) = .ok (.int 255) := by
  rfl

private theorem hexadecimal_str : intOfStr "0x_fF" 0 = .ok (.int 255) := by
  rfl

theorem hex_offset_total (offset : PyInt) :
    int_string.hex_offset(offset) ==> 255 + offset := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [int_string, lenMultBuiltinName, intCastArgs, intCastVal, intCastBase,
    hexadecimal, hexadecimal_str, add_ne_bitAnd, evalBinOpH,
    PyVCGen.binOpBeqBitAnd, PyVCGen.binOpBeqMult, setLikeRefH, funsHeapFree,
    FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList,
    Expr.heapFree, hasUnboundLocal, unboundLocalMarker, moduleGenFree,
    funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    starArgBuiltinName, starListBuiltinName, starTupleBuiltinName,
    fstringFormatBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]

theorem grouped_offset_result (offset result : PyInt)
    (run : int_string.grouped_offset(offset) ⇓ result) : result = 1024 + offset :=
  CallsTo.typed_int_eq run (grouped_offset_total offset)

end Examples.python.int_string.proof
