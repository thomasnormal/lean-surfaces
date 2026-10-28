import LeanModels.Python.Surface
import LeanModels.Python.Float64Tests

namespace Examples.python.float_lab.proof

open LeanModels LeanModels.Python

load_program float_lab from "Examples/python/float_lab/float_lab.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

private theorem initial_world :
    initWorld float_lab = (⟨#[], [], [], []⟩ : World) := by
  rfl

private theorem floatCastArgsH_str (h : Heap) (s : String) :
    floatCastArgsH h [.str s] = floatCastArgs [.str s] := by
  rfl

private theorem float_ne_fstring : ("float" == fstringFormatBuiltinName) = false := by decide
private theorem float_ne_lenMult : ("float" == lenMultBuiltinName) = false := by decide
private theorem float_ne_starArg : ("float" == starArgBuiltinName) = false := by decide
private theorem float_ne_starTuple : ("float" == starTupleBuiltinName) = false := by decide
private theorem float_ne_starList : ("float" == starListBuiltinName) = false := by decide

private theorem divmod_ne_fstring : ("divmod" == fstringFormatBuiltinName) = false := by decide
private theorem divmod_ne_lenMult : ("divmod" == lenMultBuiltinName) = false := by decide
private theorem divmod_ne_starArg : ("divmod" == starArgBuiltinName) = false := by decide
private theorem divmod_ne_starTuple : ("divmod" == starTupleBuiltinName) = false := by decide
private theorem divmod_ne_starList : ("divmod" == starListBuiltinName) = false := by decide

theorem tenth :
    float_lab.tenth() ==> Float64.ofBits 0x3fb999999999999a := by
  exact ⟨32, rfl⟩

theorem integer_true :
    float_lab.integer_true() ==> Float64.ofBits 0x4004000000000000 := by
  exact ⟨32, rfl⟩

theorem default_passthrough (value : PyFloat) :
    float_lab.default(value) ==> value := by
  exact ⟨32, rfl⟩

theorem addition :
    float_lab.addition() ==> Float64.ofBits 0x4008000000000000 := by
  exact ⟨32, rfl⟩

theorem finite_keys :
    float_lab.finite_keys() ==>
      Val.tuple #[.str "one", .str "one", .str "one", .int 2] := by
  exact ⟨64, rfl⟩

theorem nested_finite_keys :
    float_lab.nested_finite_keys() ==>
      Val.tuple #[.str "one", .str "one", .int 1] := by
  exact ⟨64, rfl⟩

theorem set_finite_keys :
    float_lab.set_finite_keys() ==>
      Val.tuple #[.bool true, .bool true, .int 2] := by
  exact ⟨64, rfl⟩

theorem nan_equality :
    float_lab.nan_equality_still_loud(Float64.ofBits 0x7ff8000000000000) ==> false := by
  exact ⟨32, rfl⟩

theorem nan_sort :
    float_lab.nan_sort_still_loud(Float64.ofBits 0x7ff8000000000000) ==>
      Val.list #[.float (Float64.ofBits 0x4000000000000000),
        .float (Float64.ofBits 0x7ff8000000000000),
        .float (Float64.ofBits 0x3ff0000000000000)] := by
  exact ⟨64, rfl⟩

private theorem add_quarter :
    Float64.arithmetic .add (Float64.ofBits 0x3fe0000000000000)
      (Float64.ofBits 0x3fd0000000000000) = .ok (Float64.ofBits 0x3fe8000000000000) := rfl

private theorem subtract_eighth :
    Float64.arithmetic .sub (Float64.ofBits 0x3fe8000000000000)
      (Float64.ofBits 0x3fc0000000000000) = .ok (Float64.ofBits 0x3fe4000000000000) := rfl

private theorem multiply_negative_two :
    Float64.arithmetic .mult (Float64.ofBits 0x3fe4000000000000)
      (Float64.ofBits 0xc000000000000000) = .ok (Float64.ofBits 0xbff4000000000000) := rfl

theorem augmented :
    float_lab.augmented() ==> Float64.ofBits 0xbff4000000000000 := by
  have addStep : Float64.arithmetic .add ⟨0x3fe0000000000000⟩ ⟨0x3fd0000000000000⟩ =
      .ok ⟨0x3fe8000000000000⟩ := add_quarter
  have subtractStep : Float64.arithmetic .sub ⟨0x3fe8000000000000⟩ ⟨0x3fc0000000000000⟩ =
      .ok ⟨0x3fe4000000000000⟩ := subtract_eighth
  have multiplyStep : Float64.arithmetic .mult ⟨0x3fe4000000000000⟩ ⟨0xc000000000000000⟩ =
      .ok ⟨0xbff4000000000000⟩ := multiply_negative_two
  have negateStep : (⟨0x4000000000000000⟩ : Float64).neg = ⟨0xc000000000000000⟩ := rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [float_lab, evalBinOpH, setLikeRefH, evalFloatArithmetic, floatNumber,
    addStep, subtractStep, multiplyStep, negateStep]
  rfl

theorem mixed_rounding :
    float_lab.mixed_rounding() ==> Float64.ofBits 0x4340000000000000 := by
  exact ⟨32, rfl⟩

theorem cancel (value : PyFloat) (finite : value.exponent ≠ 2047) :
    float_lab.cancel(value) ==> Float64.ofBits 0 := by
  have notNaN : value.isNaN = false := by
    simp [Float64.isNaN, finite]
  have notInvalid :
      floatArithmeticInvalid .sub value value = false := by
    simp [floatArithmeticInvalid, Float64.isInf, finite]
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [float_lab, evalBinOpH, setLikeRefH, evalFloatArithmetic, floatNumber,
    Float64.arithmetic_sub_self, finite, notNaN, notInvalid]

theorem constructor_identity (value : PyFloat) :
    float_lab.constructor(value) ==> value := by
  exact ⟨32, rfl⟩

theorem constructor_zero :
    float_lab.constructor_zero() ==> Float64.ofBits 0 := by
  exact ⟨32, rfl⟩

theorem constructor_tenth :
    float_lab.constructor_tenth() ==> Float64.ofBits 0x3fb999999999999a := by
  exact ⟨32, rfl⟩

theorem constructor_unicode :
    float_lab.constructor_unicode() ==> Float64.ofBits 0x3fb999999999999a := by
  have parsed : Float64.fromText "\u3000٠.١\u3000" =
      .ok (Float64.ofBits 0x3fb999999999999a) := rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [initial_world]
  rw [callIn.eq_2]
  py_simp [float_lab, floatCastArgs, floatCastVal, floatCastArgsH_str, parsed,
    float_ne_fstring, float_ne_lenMult, float_ne_starArg, float_ne_starTuple,
    float_ne_starList, funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList,
    Stmt.heapFree, Expr.heapFreeList, Expr.heapFree, moduleGenFree,
    funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    topLevelDefFree, Stmt.defFreeList, Stmt.defFree, starArgBuiltinName,
    starListBuiltinName, starTupleBuiltinName, fstringFormatBuiltinName,
    lenMultBuiltinName, hasUnboundLocal, unboundLocalMarker,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Env.lookup, lookupG, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB]


theorem constructor_rounding :
    float_lab.constructor_rounding() ==> Float64.ofBits 0x4340000000000000 := by
  exact ⟨32, rfl⟩

theorem constructor_invalid_caught :
    float_lab.constructor_invalid_caught() ==> (17 : PyInt) := by
  have invalid : Float64.fromText "1._0" = .error .invalid := rfl
  have rendered : LeanModels.Python.reprStr "1._0" = some "'1._0'" := rfl
  have failure : floatCastArgs [.str "1._0"] =
      .exn (.valueError "could not convert string to float: '1._0'") := by
    simp only [floatCastArgs, floatCastVal, invalid, rendered]
    congr 2
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [initial_world]
  rw [callIn.eq_2]
  py_simp [float_lab, failure, floatCastArgsH_str,
    float_ne_fstring, float_ne_lenMult, float_ne_starArg, float_ne_starTuple,
    float_ne_starList, funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList,
    Stmt.heapFree, Expr.heapFreeList, Expr.heapFree, moduleGenFree,
    funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    topLevelDefFree, Stmt.defFreeList, Stmt.defFree, starArgBuiltinName,
    starListBuiltinName, starTupleBuiltinName, fstringFormatBuiltinName,
    lenMultBuiltinName, hasUnboundLocal, unboundLocalMarker,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Env.lookup, lookupG, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB, excHandlerNames, excHandlerTuple, excHandlerAdmitted, excHandlerMatches,
    userExcCatches, classAtExc, builtinExcNameCatches]


theorem infinity_literal :
    float_lab.nonfinite_division_still_loud() ==> Float64.ofBits 0x7ff0000000000000 := by
  exact ⟨32, rfl⟩

theorem infinite_quotient :
    float_lab.infinite_quotient() ==> Float64.ofBits 0xfff0000000000000 := by
  exact ⟨32, rfl⟩

theorem infinite_denominator :
    float_lab.infinite_denominator() ==> Float64.ofBits 0x8000000000000000 := by
  exact ⟨32, rfl⟩

theorem infinite_augmented :
    float_lab.infinite_augmented() ==> Float64.ofBits 0 := by
  exact ⟨32, rfl⟩

theorem infinite_zero_caught :
    float_lab.infinite_zero_caught() ==> (19 : PyInt) := by
  exact ⟨32, rfl⟩

theorem count_nan_head :
    float_lab.count_head(Float64.ofBits 0x7ff8000000000000,
      Float64.ofBits 0x3ff0000000000000) ==> Float64.ofBits 0x7ff8000000000000 := by
  exact ⟨64, rfl⟩

theorem count_infinity_head :
    float_lab.count_head(Float64.ofBits 0x7ff0000000000000,
      Float64.ofBits 0x3ff0000000000000) ==> Float64.ofBits 0x7ff0000000000000 := by
  exact ⟨64, rfl⟩

theorem division_nan_left :
    float_lab.divide(Float64.ofBits 0x7ff0000000000001,
      Float64.ofBits 0x3ff0000000000000) ==> Float64.ofBits 0x7ff8000000000001 := by
  exact ⟨32, rfl⟩

theorem division_nan_right :
    float_lab.divide(Float64.ofBits 0x3ff0000000000000,
      Float64.ofBits 0xfff0000000000001) ==> Float64.ofBits 0xfff8000000000001 := by
  exact ⟨32, rfl⟩

theorem indeterminate_division :
    float_lab.indeterminate_division_still_loud() ==> Float64.ofBits 0xfff8000000000000 := by
  exact ⟨32, rfl⟩

theorem floor_tenth :
    float_lab.floor_tenth() ==> Float64.ofBits 0x4022000000000000 := by
  have floorStep : Float64.floorRemWithNaN ⟨0x3ff0000000000000⟩ ⟨0x3fb999999999999a⟩ =
      .ok (⟨0x4022000000000000⟩, ⟨0x3fb9999999999996⟩) :=
    rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [float_lab, evalBinOpH, setLikeRefH, evalFloatDivmod, floatNumber, Float64.ofBits, floorStep]

theorem remainder_tenth :
    float_lab.remainder_tenth() ==> Float64.ofBits 0x3fb9999999999996 := by
  have floorStep : Float64.floorRemWithNaN ⟨0x3ff0000000000000⟩ ⟨0x3fb999999999999a⟩ =
      .ok (⟨0x4022000000000000⟩, ⟨0x3fb9999999999996⟩) :=
    rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [float_lab, evalBinOpH, setLikeRefH, evalFloatDivmod, floatNumber, Float64.ofBits, floorStep]

theorem floor_infinite :
    float_lab.floor_infinite() ==> Float64.ofBits 0xbff0000000000000 := by
  have floorStep : Float64.floorRemWithNaN ⟨0x4014000000000000⟩ ⟨0xfff0000000000000⟩ =
      .ok (⟨0xbff0000000000000⟩, ⟨0xfff0000000000000⟩) := rfl
  have parsed : Float64.fromText "-inf" = .ok (Float64.ofBits 0xfff0000000000000) := rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [initial_world]
  rw [callIn.eq_2]
  py_simp [float_lab, evalBinOpH, setLikeRefH, floatCastArgsH_str,
    floatCastArgs, floatCastVal, evalFloatDivmod, floatNumber,
    Float64.ofBits, floorStep, parsed,
    float_ne_fstring, float_ne_lenMult, float_ne_starArg, float_ne_starTuple,
    float_ne_starList, funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList,
    Stmt.heapFree, Expr.heapFreeList, Expr.heapFree, moduleGenFree,
    funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    topLevelDefFree, Stmt.defFreeList, Stmt.defFree, starArgBuiltinName,
    starListBuiltinName, starTupleBuiltinName, fstringFormatBuiltinName,
    lenMultBuiltinName, hasUnboundLocal, unboundLocalMarker,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Env.lookup, lookupG, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB]


theorem remainder_infinite :
    float_lab.remainder_infinite() ==> Float64.ofBits 0xfff0000000000000 := by
  have floorStep : Float64.floorRemWithNaN ⟨0x4014000000000000⟩ ⟨0xfff0000000000000⟩ =
      .ok (⟨0xbff0000000000000⟩, ⟨0xfff0000000000000⟩) := rfl
  have parsed : Float64.fromText "-inf" = .ok (Float64.ofBits 0xfff0000000000000) := rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [initial_world]
  rw [callIn.eq_2]
  py_simp [float_lab, evalBinOpH, setLikeRefH, floatCastArgsH_str,
    floatCastArgs, floatCastVal, evalFloatDivmod, floatNumber,
    Float64.ofBits, floorStep, parsed,
    float_ne_fstring, float_ne_lenMult, float_ne_starArg, float_ne_starTuple,
    float_ne_starList, funsHeapFree, FunctionDefn.heapFree, Stmt.heapFreeList,
    Stmt.heapFree, Expr.heapFreeList, Expr.heapFree, moduleGenFree,
    funsGenAllocFree, Stmt.genAllocFree, Stmt.genAllocFreeList,
    topLevelDefFree, Stmt.defFreeList, Stmt.defFree, starArgBuiltinName,
    starListBuiltinName, starTupleBuiltinName, fstringFormatBuiltinName,
    lenMultBuiltinName, hasUnboundLocal, unboundLocalMarker,
    isLoweredBuiltinName, isPyBuiltinName, flattenStarRun,
    flattenStarCallArgs, Env.lookup, lookupG, Run.bind, Run.liftRes,
    Run.toPublic, RVal.freezeB]


theorem floor_nan_pair :
    float_lab.floor_pair(Float64.ofBits 0x7ff8000000000001,
      Float64.ofBits 0x3ff0000000000000) ==>
      Val.tuple #[
        .float (Float64.ofBits 0x7ff8000000000001),
        .float (Float64.ofBits 0x7ff8000000000001),
        .tuple #[
          .float (Float64.ofBits 0x7ff8000000000001),
          .float (Float64.ofBits 0x7ff8000000000001)
        ]
      ] := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [initial_world]
  rw [callIn.eq_2]
  have nanStep : Float64.floorRemWithNaN ⟨0x7ff8000000000001⟩ ⟨0x3ff0000000000000⟩ =
      .ok (⟨0x7ff8000000000001⟩, ⟨0x7ff8000000000001⟩) := rfl
  py_simp [float_lab, evalBinOpH, setLikeRefH, evalFloatDivmod, floatNumber,
    Float64.ofBits, nanStep,
    divmod_ne_fstring, divmod_ne_lenMult, divmod_ne_starArg,
    divmod_ne_starTuple, divmod_ne_starList, funsHeapFree,
    FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, topLevelDefFree,
    Stmt.defFreeList, Stmt.defFree, starArgBuiltinName, starListBuiltinName,
    starTupleBuiltinName, fstringFormatBuiltinName, lenMultBuiltinName,
    hasUnboundLocal, unboundLocalMarker, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Env.lookup,
    lookupG, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB]


private theorem remainder_nine_four :
    Float64.floorRem (Float64.ofBits 0x4022000000000000)
      (Float64.ofBits 0x4010000000000000) =
      .ok (Float64.ofBits 0x4000000000000000, Float64.ofBits 0x3ff0000000000000) := rfl

theorem floor_augmented :
    float_lab.floor_augmented() ==> Float64.ofBits 0x3ff0000000000000 := by
  have floorStep : Float64.floorRemWithNaN ⟨0x3ff0000000000000⟩ ⟨0x3fb999999999999a⟩ =
      .ok (⟨0x4022000000000000⟩, ⟨0x3fb9999999999996⟩) :=
    rfl
  have remainderStep : Float64.floorRemWithNaN ⟨0x4022000000000000⟩ ⟨0x4010000000000000⟩ =
      .ok (⟨0x4000000000000000⟩, ⟨0x3ff0000000000000⟩) := by rfl
  refine ⟨32, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [float_lab, evalBinOpH, setLikeRefH, evalFloatDivmod, floatNumber, Float64.ofBits, floorStep, remainderStep]

theorem floor_zero_caught :
    float_lab.floor_zero_caught(2) ==> (23 : PyInt) := by
  have negateStep : (⟨0⟩ : Float64).neg = ⟨0x8000000000000000⟩ := rfl
  have zeroStep : Float64.floorRemWithNaN ⟨0x3ff0000000000000⟩ ⟨0x8000000000000000⟩ =
      .error .zeroDivision := rfl
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [initial_world]
  rw [callIn.eq_2]
  py_simp [float_lab, evalBinOpH, setLikeRefH, divmodArgs, evalFloatDivmod,
    floatNumber, negateStep, zeroStep,
    divmod_ne_fstring, divmod_ne_lenMult, divmod_ne_starArg,
    divmod_ne_starTuple, divmod_ne_starList, funsHeapFree,
    FunctionDefn.heapFree, Stmt.heapFreeList, Stmt.heapFree,
    Expr.heapFreeList, Expr.heapFree, moduleGenFree, funsGenAllocFree,
    Stmt.genAllocFree, Stmt.genAllocFreeList, topLevelDefFree,
    Stmt.defFreeList, Stmt.defFree, starArgBuiltinName, starListBuiltinName,
    starTupleBuiltinName, fstringFormatBuiltinName, lenMultBuiltinName,
    hasUnboundLocal, unboundLocalMarker, isLoweredBuiltinName,
    isPyBuiltinName, flattenStarRun, flattenStarCallArgs, Env.lookup,
    lookupG, Run.bind, Run.liftRes, Run.toPublic, RVal.freezeB, excHandlerNames, excHandlerTuple, excHandlerAdmitted, excHandlerMatches,
    userExcCatches, classAtExc, builtinExcNameCatches]


#print axioms floor_tenth
#print axioms remainder_tenth
#print axioms floor_infinite
#print axioms remainder_infinite
#print axioms floor_nan_pair
#print axioms floor_augmented
#print axioms floor_zero_caught
#print axioms remainder_nine_four
#print axioms infinity_literal
#print axioms infinite_quotient
#print axioms infinite_denominator
#print axioms infinite_augmented
#print axioms infinite_zero_caught
#print axioms count_nan_head
#print axioms count_infinity_head
#print axioms division_nan_left
#print axioms division_nan_right
#print axioms indeterminate_division
#print axioms constructor_identity
#print axioms constructor_zero
#print axioms constructor_tenth
#print axioms constructor_unicode
#print axioms constructor_rounding
#print axioms constructor_invalid_caught
#print axioms tenth
#print axioms integer_true
#print axioms default_passthrough
#print axioms addition
#print axioms augmented
#print axioms mixed_rounding
#print axioms cancel
#print axioms add_quarter
#print axioms subtract_eighth
#print axioms multiply_negative_two

end Examples.python.float_lab.proof
