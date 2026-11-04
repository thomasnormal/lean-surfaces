import LeanModels.Python.Surface

namespace Examples.python.round_lab.proof

open LeanModels LeanModels.Python

load_program round_lab from "Examples/python/round_lab/round_lab.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

private theorem round_ne_fstring : ("round" == fstringFormatBuiltinName) = false := by decide
private theorem round_ne_lenMult : ("round" == lenMultBuiltinName) = false := by decide
private theorem round_ne_starArg : ("round" == starArgBuiltinName) = false := by decide
private theorem round_ne_starTuple : ("round" == starTupleBuiltinName) = false := by decide
private theorem round_ne_starList : ("round" == starListBuiltinName) = false := by decide
private theorem round_float_zero_value :
    roundFloatZero (Float64.ofBits 0x3ff8000000000000) =
      .ok (.float (Float64.ofBits 0x4000000000000000)) := by rfl
private theorem round_float_one_value :
    roundFloatOne (Float64.ofBits 0x4005666666666666) =
      .ok (.float (Float64.ofBits 0x400599999999999a)) := by rfl
private theorem round_float_two_value :
    roundFloatTwo (Float64.ofBits 0x3ff3c083126e978d) =
      .ok (.float (Float64.ofBits 0x3ff3ae147ae147ae)) := by rfl
private theorem round_float_three_value :
    roundFloatThree (Float64.ofBits 0x3ff3c083126e978d) =
      .ok (.float (Float64.ofBits 0x3ff3be76c8b43958)) := by rfl
private theorem round_float_four_value :
    roundFloatFour (Float64.ofBits 0x3ff3c0c1fc8f3238) =
      .ok (.float (Float64.ofBits 0x3ff3c0ebedfa43fe)) := by rfl

theorem round_float_half :
    round_lab.round_float(Float64.ofBits 0x3fe0000000000000) ==> Val.int 0 := by
  exact ⟨32, rfl⟩

theorem round_float_ties :
    round_lab.round_float_ties() ==>
      Val.tuple #[Val.int 0, Val.int 2, Val.int 2, Val.int 0, Val.int (-2), Val.int (-2)] := by
  exact ⟨32, rfl⟩

theorem round_float_large :
    round_lab.round_float_large() ==>
      Val.int 1000000000000000052504760255204420248704468581108159154915854115511802457988908195786371375080447864043704443832883878176942523235360430575644792184786706982848387200926575803737830233794788090059368953234970799945081119038967640880074652742780142494579258788820056842838115669472196386865459400540160 := by
  exact ⟨128, rfl⟩

theorem round_float_nan :
    round_lab.round_float_nan() ==>!
      (.valueError "cannot convert float NaN to integer") := by
  exact ⟨32, rfl⟩

theorem round_float_infinity :
    round_lab.round_float_infinity() ==>!
      (.overflowError "cannot convert float infinity to integer") := by
  exact ⟨32, rfl⟩

theorem round_float_zero :
    round_lab.round_float_zero(Float64.ofBits 0x3ff8000000000000) ==>
      Val.float (Float64.ofBits 0x4000000000000000) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne, roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundRatioInt, roundEvenNat,
    round_float_zero_value, Float64.fromInt, Float64.ofBits, funsHeapFree,
    FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList,
    Expr.heapFree, hasUnboundLocal, unboundLocalMarker, moduleGenFree,
    funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun, flattenStarCallArgs,
    Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_int_zero :
    round_lab.round_int_zero(7) ==> Val.int 7 := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne, roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundRatioInt, roundEvenNat,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_bool_zero :
    round_lab.round_bool_zero(true) ==> Val.int 1 := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne, roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundRatioInt, roundEvenNat,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_int_positive :
    round_lab.round_int_positive(7) ==> Val.int 7 := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne, roundDigitsNonnegative,
    roundDigitsZero, roundDigitsOne, roundRatioInt, roundEvenNat, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun, flattenStarCallArgs,
    Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_bool_positive :
    round_lab.round_bool_positive(true) ==> Val.int 1 := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne, roundDigitsNonnegative,
    roundDigitsZero, roundDigitsOne, roundRatioInt, roundEvenNat, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun, flattenStarCallArgs,
    Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_one :
    round_lab.round_float_one(Float64.ofBits 0x4005666666666666) ==>
      Val.float (Float64.ofBits 0x400599999999999a) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundRatioInt,
    roundEvenNat, round_float_one_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun, flattenStarCallArgs,
    Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_two :
    round_lab.round_float_two(Float64.ofBits 0x3ff3c083126e978d) ==>
      Val.float (Float64.ofBits 0x3ff3ae147ae147ae) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundDigitsNonnegative, roundDigitsZero, roundDigitsOne,
    roundDigitsTwo, roundRatioInt, roundEvenNat, round_float_two_value,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_three :
    round_lab.round_float_three(Float64.ofBits 0x3ff3c083126e978d) ==>
      Val.float (Float64.ofBits 0x3ff3be76c8b43958) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundDigitsNonnegative, roundDigitsZero,
    roundDigitsOne, roundDigitsTwo, roundDigitsThree, roundRatioInt,
    roundEvenNat, round_float_three_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun, flattenStarCallArgs,
    Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_four :
    round_lab.round_float_four(Float64.ofBits 0x3ff3c0c1fc8f3238) ==>
      Val.float (Float64.ofBits 0x3ff3c0ebedfa43fe) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundDigitsNonnegative,
    roundDigitsZero, roundDigitsOne, roundDigitsTwo, roundDigitsThree,
    roundDigitsFour, roundRatioInt, roundEvenNat, round_float_four_value,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

end Examples.python.round_lab.proof
