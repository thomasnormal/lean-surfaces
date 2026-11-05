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
private theorem round_float_five_value :
    roundFloatFive (Float64.ofBits 0x3ff3c0c9539b8887) =
      .ok (.float (Float64.ofBits 0x3ff3c0cc78e9f6a9)) := by rfl
private theorem round_float_six_value :
    roundFloatSix (Float64.ofBits 0x3ff3c0ca2a5b1d5d) =
      .ok (.float (Float64.ofBits 0x3ff3c0ca600b0293)) := by rfl
private theorem round_float_seven_value :
    roundFloatSeven (Float64.ofBits 0x3ff3c0ca4283de1b) =
      .ok (.float (Float64.ofBits 0x3ff3c0ca45330ff8)) := by rfl
private theorem round_float_eight_value :
    roundFloatEight (Float64.ofBits 0x3ff3c0ca43db770a) =
      .ok (.float (Float64.ofBits 0x3ff3c0ca45330ff8)) := by rfl
private theorem round_float_nine_value :
    roundFloatNine (Float64.ofBits 0x3ff3c0ca43db770a) =
      .ok (.float (Float64.ofBits 0x3ff3c0ca43db770a)) := by rfl
private theorem round_float_ten_value :
    roundFloatTen (Float64.ofBits 0x3ff3c0ca43bc8a8e) =
      .ok (.float (Float64.ofBits 0x3ff3c0ca43bffa2a)) := by rfl
private theorem round_float_eleven_value :
    roundFloatEleven (Float64.ofBits 0x3ff3c0ca43bce284) =
      .ok (.float (Float64.ofBits 0x3ff3c0ca43bd3a7a)) := by rfl
private theorem round_float_twelve_value :
    roundFloatTwelve (Float64.ofBits 0x3ff3c0ca43bceb50) =
      .ok (.float (Float64.ofBits 0x3ff3c0ca43bcf41b)) := by rfl
private theorem round_float_thirteen_value :
    roundFloatThirteen (Float64.ofBits 0x3ff3c0ca43bcec31) =
      .ok (.float (Float64.ofBits 0x3ff3c0ca43bced12)) := by rfl
private theorem round_float_fourteen_value :
    roundFloatFourteen (Float64.ofBits 0x3ff3c0ca43bcec47) =
      .ok (.float (Float64.ofBits 0x3ff3c0ca43bcec31)) := by rfl
private theorem round_float_fifteen_value :
    roundFloatFifteen (Float64.ofBits 0x3ff3c0ca43bcec4a) =
      .ok (.float (Float64.ofBits 0x3ff3c0ca43bcec4c)) := by rfl
private theorem round_float_sixteen_value :
    roundFloatSixteen (Float64.ofBits 0xbfcc61aba94c9000) =
      .ok (.float (Float64.ofBits 0xbfcc61aba94c8fff)) := by rfl
private theorem round_float_seventeen_value :
    roundFloatSeventeen (Float64.ofBits 0x3f4b6113d6000000) =
      .ok (.float (Float64.ofBits 0x3f4b6113d600001c)) := by rfl
private theorem round_float_eighteen_value :
    roundFloatEighteen (Float64.ofBits 0x3f296619b1800000) =
      .ok (.float (Float64.ofBits 0x3f296619b17ffff2)) := by rfl
private theorem round_float_nineteen_value :
    roundFloatNineteen (Float64.ofBits 0x1bcbc5db28669ce4) =
      .ok (.float (Float64.ofBits 0x0000000000000000)) := by rfl
private theorem round_float_twenty_value :
    roundFloatTwenty (Float64.ofBits 0xbe6abc642d583e42) =
      .ok (.float (Float64.ofBits 0xbe6abc642d583fca)) := by rfl
private theorem round_float_twenty_one_value :
    roundFloatTwentyOne (Float64.ofBits 0x000000037152faa4) =
      .ok (.float (Float64.ofBits 0x0000000000000000)) := by rfl
private theorem round_float_twenty_two_value :
    roundFloatTwentyTwo (Float64.ofBits 0xbcba01a69be3d55f) =
      .ok (.float (Float64.ofBits 0xbcba01a6bb68a42c)) := by rfl
private theorem round_float_twenty_three_value :
    roundFloatTwentyThree (Float64.ofBits 0x1ea2921e74374449) =
      .ok (.float (Float64.ofBits 0x0000000000000000)) := by rfl
private theorem round_float_twenty_four_value :
    roundFloatTwentyFour (Float64.ofBits 0x8e6ad9eaa6aa45d4) =
      .ok (.float (Float64.ofBits 0x8000000000000000)) := by rfl
private theorem round_float_twenty_five_value :
    roundFloatTwentyFive (Float64.ofBits 0x000044fa709cccc2) =
      .ok (.float (Float64.ofBits 0x0000000000000000)) := by rfl
private theorem round_float_twenty_six_value :
    roundFloatTwentySix (Float64.ofBits 0x8328aa3794629f05) =
      .ok (.float (Float64.ofBits 0x8000000000000000)) := by rfl
private theorem round_float_twenty_seven_value :
    roundFloatTwentySeven (Float64.ofBits 0x3a2385852121f802) =
      .ok (.float (Float64.ofBits 0x0000000000000000)) := by rfl
private theorem round_float_twenty_eight_value :
    roundFloatTwentyEight (Float64.ofBits 0x2c17b3dc78313e22) =
      .ok (.float (Float64.ofBits 0x0000000000000000)) := by rfl
private theorem round_float_twenty_nine_value :
    roundFloatTwentyNine (Float64.ofBits 0x347beee1956a049f) =
      .ok (.float (Float64.ofBits 0x0000000000000000)) := by rfl

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

theorem round_float_five :
    round_lab.round_float_five(Float64.ofBits 0x3ff3c0c9539b8887) ==>
      Val.float (Float64.ofBits 0x3ff3c0cc78e9f6a9) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundDigitsTwo,
    roundDigitsThree, roundDigitsFour, roundDigitsFive, roundRatioInt,
    roundEvenNat, round_float_five_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun, flattenStarCallArgs,
    Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_six :
    round_lab.round_float_six(Float64.ofBits 0x3ff3c0ca2a5b1d5d) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca600b0293) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundDigitsNonnegative, roundDigitsZero, roundDigitsOne,
    roundDigitsTwo, roundDigitsThree, roundDigitsFour, roundDigitsFive,
    roundDigitsSix, roundRatioInt, roundEvenNat, round_float_six_value,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_seven :
    round_lab.round_float_seven(Float64.ofBits 0x3ff3c0ca4283de1b) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca45330ff8) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundDigitsNonnegative, roundDigitsZero,
    roundDigitsOne, roundDigitsTwo, roundDigitsThree, roundDigitsFour,
    roundDigitsFive, roundDigitsSix, roundDigitsSeven, roundRatioInt,
    roundEvenNat, round_float_seven_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun, flattenStarCallArgs,
    Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_eight :
    round_lab.round_float_eight(Float64.ofBits 0x3ff3c0ca43db770a) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca45330ff8) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundDigitsNonnegative,
    roundDigitsZero, roundDigitsOne, roundDigitsTwo, roundDigitsThree,
    roundDigitsFour, roundDigitsFive, roundDigitsSix, roundDigitsSeven,
    roundDigitsEight, roundRatioInt, roundEvenNat, round_float_eight_value,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_nine :
    round_lab.round_float_nine(Float64.ofBits 0x3ff3c0ca43db770a) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43db770a) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundDigitsTwo,
    roundDigitsThree, roundDigitsFour, roundDigitsFive, roundDigitsSix,
    roundDigitsSeven, roundDigitsEight, roundDigitsNine, roundRatioInt,
    roundEvenNat, round_float_nine_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun, flattenStarCallArgs,
    Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_ten :
    round_lab.round_float_ten(Float64.ofBits 0x3ff3c0ca43bc8a8e) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bffa2a) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundDigitsNonnegative, roundDigitsZero, roundDigitsOne,
    roundDigitsTwo, roundDigitsThree, roundDigitsFour, roundDigitsFive,
    roundDigitsSix, roundDigitsSeven, roundDigitsEight, roundDigitsNine,
    roundDigitsTen, roundRatioInt, roundEvenNat, round_float_ten_value,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_eleven :
    round_lab.round_float_eleven(Float64.ofBits 0x3ff3c0ca43bce284) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bd3a7a) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundDigitsNonnegative, roundDigitsZero,
    roundDigitsOne, roundDigitsTwo, roundDigitsThree, roundDigitsFour,
    roundDigitsFive, roundDigitsSix, roundDigitsSeven, roundDigitsEight,
    roundDigitsNine, roundDigitsTen, roundDigitsEleven, roundRatioInt,
    roundEvenNat, round_float_eleven_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_twelve :
    round_lab.round_float_twelve(Float64.ofBits 0x3ff3c0ca43bceb50) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bcf41b) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundDigitsNonnegative,
    roundDigitsZero, roundDigitsOne, roundDigitsTwo, roundDigitsThree,
    roundDigitsFour, roundDigitsFive, roundDigitsSix, roundDigitsSeven,
    roundDigitsEight, roundDigitsNine, roundDigitsTen, roundDigitsEleven,
    roundDigitsTwelve, roundRatioInt, roundEvenNat, round_float_twelve_value,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_thirteen :
    round_lab.round_float_thirteen(Float64.ofBits 0x3ff3c0ca43bcec31) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bced12) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundDigitsTwo,
    roundDigitsThree, roundDigitsFour, roundDigitsFive, roundDigitsSix,
    roundDigitsSeven, roundDigitsEight, roundDigitsNine, roundDigitsTen,
    roundDigitsEleven, roundDigitsTwelve, roundDigitsThirteen, roundRatioInt,
    roundEvenNat, round_float_thirteen_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_fourteen :
    round_lab.round_float_fourteen(Float64.ofBits 0x3ff3c0ca43bcec47) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bcec31) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundDigitsNonnegative, roundDigitsZero, roundDigitsOne,
    roundDigitsTwo, roundDigitsThree, roundDigitsFour, roundDigitsFive,
    roundDigitsSix, roundDigitsSeven, roundDigitsEight, roundDigitsNine,
    roundDigitsTen, roundDigitsEleven, roundDigitsTwelve, roundDigitsThirteen,
    roundDigitsFourteen, roundRatioInt, roundEvenNat, round_float_fourteen_value,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_fifteen :
    round_lab.round_float_fifteen(Float64.ofBits 0x3ff3c0ca43bcec4a) ==>
      Val.float (Float64.ofBits 0x3ff3c0ca43bcec4c) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundDigitsNonnegative,
    roundDigitsZero, roundDigitsOne, roundDigitsTwo, roundDigitsThree,
    roundDigitsFour, roundDigitsFive, roundDigitsSix, roundDigitsSeven,
    roundDigitsEight, roundDigitsNine, roundDigitsTen, roundDigitsEleven,
    roundDigitsTwelve, roundDigitsThirteen, roundDigitsFourteen,
    roundDigitsFifteen, roundRatioInt, roundEvenNat, round_float_fifteen_value,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_sixteen :
    round_lab.round_float_sixteen(Float64.ofBits 0xbfcc61aba94c9000) ==>
      Val.float (Float64.ofBits 0xbfcc61aba94c8fff) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundDigitsTwo,
    roundDigitsThree, roundDigitsFour, roundDigitsFive, roundDigitsSix,
    roundDigitsSeven, roundDigitsEight, roundDigitsNine, roundDigitsTen,
    roundDigitsEleven, roundDigitsTwelve, roundDigitsThirteen,
    roundDigitsFourteen, roundDigitsFifteen, roundDigitsSixteen, roundRatioInt,
    roundEvenNat, round_float_sixteen_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_seventeen :
    round_lab.round_float_seventeen(Float64.ofBits 0x3f4b6113d6000000) ==>
      Val.float (Float64.ofBits 0x3f4b6113d600001c) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundDigitsNonnegative, roundDigitsZero,
    roundDigitsOne, roundDigitsTwo, roundDigitsThree, roundDigitsFour,
    roundDigitsFive, roundDigitsSix, roundDigitsSeven, roundDigitsEight,
    roundDigitsNine, roundDigitsTen, roundDigitsEleven, roundDigitsTwelve,
    roundDigitsThirteen, roundDigitsFourteen, roundDigitsFifteen,
    roundDigitsSixteen, roundDigitsSeventeen, roundRatioInt, roundEvenNat,
    round_float_seventeen_value, Float64.fromInt, Float64.ofBits, funsHeapFree,
    FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_eighteen :
    round_lab.round_float_eighteen(Float64.ofBits 0x3f296619b1800000) ==>
      Val.float (Float64.ofBits 0x3f296619b17ffff2) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundDigitsNonnegative,
    roundDigitsZero, roundDigitsOne, roundDigitsTwo, roundDigitsThree,
    roundDigitsFour, roundDigitsFive, roundDigitsSix, roundDigitsSeven,
    roundDigitsEight, roundDigitsNine, roundDigitsTen, roundDigitsEleven,
    roundDigitsTwelve, roundDigitsThirteen, roundDigitsFourteen,
    roundDigitsFifteen, roundDigitsSixteen, roundDigitsSeventeen,
    roundDigitsEighteen, roundRatioInt, roundEvenNat,
    round_float_eighteen_value, Float64.fromInt, Float64.ofBits, funsHeapFree,
    FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_nineteen :
    round_lab.round_float_nineteen(Float64.ofBits 0x1bcbc5db28669ce4) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundFloatNineteen,
    roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundDigitsTwo,
    roundDigitsThree, roundDigitsFour, roundDigitsFive, roundDigitsSix,
    roundDigitsSeven, roundDigitsEight, roundDigitsNine, roundDigitsTen,
    roundDigitsEleven, roundDigitsTwelve, roundDigitsThirteen,
    roundDigitsFourteen, roundDigitsFifteen, roundDigitsSixteen,
    roundDigitsSeventeen, roundDigitsEighteen, roundDigitsNineteen,
    roundRatioInt, roundEvenNat, round_float_nineteen_value, Float64.fromInt,
    Float64.ofBits, funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList,
    Stmt.heapFree, Expr.heapFreeList, Expr.heapFree, hasUnboundLocal,
    unboundLocalMarker, moduleGenFree, funsGenAllocFree, Stmt.genAllocFree,
    Stmt.genAllocFreeList, isLoweredBuiltinName, isPyBuiltinName,
    flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic,
    RVal.freezeB]
  all_goals rfl

theorem round_float_twenty :
    round_lab.round_float_twenty(Float64.ofBits 0xbe6abc642d583e42) ==>
      Val.float (Float64.ofBits 0xbe6abc642d583fca) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundFloatNineteen,
    roundFloatTwenty, roundDigitsNonnegative, roundDigitsZero,
    roundDigitsOne, roundDigitsTwo, roundDigitsThree, roundDigitsFour,
    roundDigitsFive, roundDigitsSix, roundDigitsSeven, roundDigitsEight,
    roundDigitsNine, roundDigitsTen, roundDigitsEleven, roundDigitsTwelve,
    roundDigitsThirteen, roundDigitsFourteen, roundDigitsFifteen,
    roundDigitsSixteen, roundDigitsSeventeen, roundDigitsEighteen,
    roundDigitsNineteen, roundDigitsTwenty, roundRatioInt, roundEvenNat,
    round_float_twenty_value, Float64.fromInt, Float64.ofBits, funsHeapFree,
    FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_twenty_one :
    round_lab.round_float_twenty_one(Float64.ofBits 0x000000037152faa4) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundFloatNineteen,
    roundFloatTwenty, roundFloatTwentyOne, roundDigitsNonnegative,
    roundDigitsZero, roundDigitsOne, roundDigitsTwo, roundDigitsThree,
    roundDigitsFour, roundDigitsFive, roundDigitsSix, roundDigitsSeven,
    roundDigitsEight, roundDigitsNine, roundDigitsTen, roundDigitsEleven,
    roundDigitsTwelve, roundDigitsThirteen, roundDigitsFourteen,
    roundDigitsFifteen, roundDigitsSixteen, roundDigitsSeventeen,
    roundDigitsEighteen, roundDigitsNineteen, roundDigitsTwenty,
    roundDigitsTwentyOne, roundRatioInt, roundEvenNat,
    round_float_twenty_one_value, Float64.fromInt, Float64.ofBits, funsHeapFree,
    FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_twenty_two :
    round_lab.round_float_twenty_two(Float64.ofBits 0xbcba01a69be3d55f) ==>
      Val.float (Float64.ofBits 0xbcba01a6bb68a42c) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundFloatNineteen,
    roundFloatTwenty, roundFloatTwentyOne, roundFloatTwentyTwo,
    roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundDigitsTwo,
    roundDigitsThree, roundDigitsFour, roundDigitsFive, roundDigitsSix,
    roundDigitsSeven, roundDigitsEight, roundDigitsNine, roundDigitsTen,
    roundDigitsEleven, roundDigitsTwelve, roundDigitsThirteen,
    roundDigitsFourteen, roundDigitsFifteen, roundDigitsSixteen,
    roundDigitsSeventeen, roundDigitsEighteen, roundDigitsNineteen,
    roundDigitsTwenty, roundDigitsTwentyOne, roundDigitsTwentyTwo,
    roundRatioInt, roundEvenNat, round_float_twenty_two_value,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_twenty_three :
    round_lab.round_float_twenty_three(Float64.ofBits 0x1ea2921e74374449) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundFloatNineteen,
    roundFloatTwenty, roundFloatTwentyOne, roundFloatTwentyTwo,
    roundFloatTwentyThree, roundDigitsNonnegative, roundDigitsZero,
    roundDigitsOne, roundDigitsTwo, roundDigitsThree, roundDigitsFour,
    roundDigitsFive, roundDigitsSix, roundDigitsSeven, roundDigitsEight,
    roundDigitsNine, roundDigitsTen, roundDigitsEleven, roundDigitsTwelve,
    roundDigitsThirteen, roundDigitsFourteen, roundDigitsFifteen,
    roundDigitsSixteen, roundDigitsSeventeen, roundDigitsEighteen,
    roundDigitsNineteen, roundDigitsTwenty, roundDigitsTwentyOne,
    roundDigitsTwentyTwo, roundDigitsTwentyThree, roundRatioInt, roundEvenNat,
    round_float_twenty_three_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_twenty_four :
    round_lab.round_float_twenty_four(Float64.ofBits 0x8e6ad9eaa6aa45d4) ==>
      Val.float (Float64.ofBits 0x8000000000000000) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundFloatNineteen,
    roundFloatTwenty, roundFloatTwentyOne, roundFloatTwentyTwo,
    roundFloatTwentyThree, roundFloatTwentyFour, roundDigitsNonnegative,
    roundDigitsZero, roundDigitsOne, roundDigitsTwo, roundDigitsThree,
    roundDigitsFour, roundDigitsFive, roundDigitsSix, roundDigitsSeven,
    roundDigitsEight, roundDigitsNine, roundDigitsTen, roundDigitsEleven,
    roundDigitsTwelve, roundDigitsThirteen, roundDigitsFourteen,
    roundDigitsFifteen, roundDigitsSixteen, roundDigitsSeventeen,
    roundDigitsEighteen, roundDigitsNineteen, roundDigitsTwenty,
    roundDigitsTwentyOne, roundDigitsTwentyTwo, roundDigitsTwentyThree,
    roundDigitsTwentyFour, roundRatioInt, roundEvenNat,
    round_float_twenty_four_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_twenty_five :
    round_lab.round_float_twenty_five(Float64.ofBits 0x000044fa709cccc2) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundFloatNineteen,
    roundFloatTwenty, roundFloatTwentyOne, roundFloatTwentyTwo,
    roundFloatTwentyThree, roundFloatTwentyFour, roundFloatTwentyFive,
    roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundDigitsTwo,
    roundDigitsThree, roundDigitsFour, roundDigitsFive, roundDigitsSix,
    roundDigitsSeven, roundDigitsEight, roundDigitsNine, roundDigitsTen,
    roundDigitsEleven, roundDigitsTwelve, roundDigitsThirteen,
    roundDigitsFourteen, roundDigitsFifteen, roundDigitsSixteen,
    roundDigitsSeventeen, roundDigitsEighteen, roundDigitsNineteen,
    roundDigitsTwenty, roundDigitsTwentyOne, roundDigitsTwentyTwo,
    roundDigitsTwentyThree, roundDigitsTwentyFour, roundDigitsTwentyFive,
    roundRatioInt, roundEvenNat, round_float_twenty_five_value,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_twenty_six :
    round_lab.round_float_twenty_six(Float64.ofBits 0x8328aa3794629f05) ==>
      Val.float (Float64.ofBits 0x8000000000000000) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundFloatNineteen,
    roundFloatTwenty, roundFloatTwentyOne, roundFloatTwentyTwo,
    roundFloatTwentyThree, roundFloatTwentyFour, roundFloatTwentyFive,
    roundFloatTwentySix, roundDigitsNonnegative, roundDigitsZero,
    roundDigitsOne, roundDigitsTwo, roundDigitsThree, roundDigitsFour,
    roundDigitsFive, roundDigitsSix, roundDigitsSeven, roundDigitsEight,
    roundDigitsNine, roundDigitsTen, roundDigitsEleven, roundDigitsTwelve,
    roundDigitsThirteen, roundDigitsFourteen, roundDigitsFifteen,
    roundDigitsSixteen, roundDigitsSeventeen, roundDigitsEighteen,
    roundDigitsNineteen, roundDigitsTwenty, roundDigitsTwentyOne,
    roundDigitsTwentyTwo, roundDigitsTwentyThree, roundDigitsTwentyFour,
    roundDigitsTwentyFive, roundDigitsTwentySix, roundRatioInt, roundEvenNat,
    round_float_twenty_six_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_twenty_seven :
    round_lab.round_float_twenty_seven(Float64.ofBits 0x3a2385852121f802) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundFloatNineteen,
    roundFloatTwenty, roundFloatTwentyOne, roundFloatTwentyTwo,
    roundFloatTwentyThree, roundFloatTwentyFour, roundFloatTwentyFive,
    roundFloatTwentySix, roundFloatTwentySeven, roundDigitsNonnegative,
    roundDigitsZero, roundDigitsOne, roundDigitsTwo, roundDigitsThree,
    roundDigitsFour, roundDigitsFive, roundDigitsSix, roundDigitsSeven,
    roundDigitsEight, roundDigitsNine, roundDigitsTen, roundDigitsEleven,
    roundDigitsTwelve, roundDigitsThirteen, roundDigitsFourteen,
    roundDigitsFifteen, roundDigitsSixteen, roundDigitsSeventeen,
    roundDigitsEighteen, roundDigitsNineteen, roundDigitsTwenty,
    roundDigitsTwentyOne, roundDigitsTwentyTwo, roundDigitsTwentyThree,
    roundDigitsTwentyFour, roundDigitsTwentyFive, roundDigitsTwentySix,
    roundDigitsTwentySeven, roundRatioInt, roundEvenNat,
    round_float_twenty_seven_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_twenty_eight :
    round_lab.round_float_twenty_eight(Float64.ofBits 0x2c17b3dc78313e22) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundFloatNineteen,
    roundFloatTwenty, roundFloatTwentyOne, roundFloatTwentyTwo,
    roundFloatTwentyThree, roundFloatTwentyFour, roundFloatTwentyFive,
    roundFloatTwentySix, roundFloatTwentySeven, roundFloatTwentyEight,
    roundDigitsNonnegative, roundDigitsZero, roundDigitsOne, roundDigitsTwo,
    roundDigitsThree, roundDigitsFour, roundDigitsFive, roundDigitsSix,
    roundDigitsSeven, roundDigitsEight, roundDigitsNine, roundDigitsTen,
    roundDigitsEleven, roundDigitsTwelve, roundDigitsThirteen,
    roundDigitsFourteen, roundDigitsFifteen, roundDigitsSixteen,
    roundDigitsSeventeen, roundDigitsEighteen, roundDigitsNineteen,
    roundDigitsTwenty, roundDigitsTwentyOne, roundDigitsTwentyTwo,
    roundDigitsTwentyThree, roundDigitsTwentyFour, roundDigitsTwentyFive,
    roundDigitsTwentySix, roundDigitsTwentySeven, roundDigitsTwentyEight,
    roundRatioInt, roundEvenNat, round_float_twenty_eight_value,
    Float64.fromInt, Float64.ofBits, funsHeapFree, FunctionDefn.heapFree,
    Stmt.heapFreeList, Stmt.heapFree, Expr.heapFreeList, Expr.heapFree,
    hasUnboundLocal, unboundLocalMarker, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Run.bind,
    Run.liftRes, Run.toPublic, RVal.freezeB]
  all_goals rfl

theorem round_float_twenty_nine :
    round_lab.round_float_twenty_nine(Float64.ofBits 0x347beee1956a049f) ==>
      Val.float (Float64.ofBits 0x0000000000000000) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [round_lab, round_ne_fstring, round_ne_lenMult, round_ne_starArg,
    round_ne_starTuple, round_ne_starList, roundFloatZero, roundFloatOne,
    roundFloatTwo, roundFloatThree, roundFloatFour, roundFloatFive,
    roundFloatSix, roundFloatSeven, roundFloatEight, roundFloatNine,
    roundFloatTen, roundFloatEleven, roundFloatTwelve, roundFloatThirteen,
    roundFloatFourteen, roundFloatFifteen, roundFloatSixteen,
    roundFloatSeventeen, roundFloatEighteen, roundFloatNineteen,
    roundFloatTwenty, roundFloatTwentyOne, roundFloatTwentyTwo,
    roundFloatTwentyThree, roundFloatTwentyFour, roundFloatTwentyFive,
    roundFloatTwentySix, roundFloatTwentySeven, roundFloatTwentyEight,
    roundFloatTwentyNine, roundDigitsNonnegative, roundDigitsZero,
    roundDigitsOne, roundDigitsTwo, roundDigitsThree, roundDigitsFour,
    roundDigitsFive, roundDigitsSix, roundDigitsSeven, roundDigitsEight,
    roundDigitsNine, roundDigitsTen, roundDigitsEleven, roundDigitsTwelve,
    roundDigitsThirteen, roundDigitsFourteen, roundDigitsFifteen,
    roundDigitsSixteen, roundDigitsSeventeen, roundDigitsEighteen,
    roundDigitsNineteen, roundDigitsTwenty, roundDigitsTwentyOne,
    roundDigitsTwentyTwo, roundDigitsTwentyThree, roundDigitsTwentyFour,
    roundDigitsTwentyFive, roundDigitsTwentySix, roundDigitsTwentySeven,
    roundDigitsTwentyEight, roundDigitsTwentyNine, roundRatioInt, roundEvenNat,
    round_float_twenty_nine_value, Float64.fromInt, Float64.ofBits,
    funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, hasUnboundLocal, unboundLocalMarker,
    moduleGenFree, funsGenAllocFree, Stmt.genAllocFree,
    Stmt.genAllocFreeList, isLoweredBuiltinName, isPyBuiltinName,
    flattenStarRun, flattenStarCallArgs, Run.bind, Run.liftRes, Run.toPublic,
    RVal.freezeB]
  all_goals rfl

end Examples.python.round_lab.proof
