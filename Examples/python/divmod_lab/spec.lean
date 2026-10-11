import Examples.python.divmod_lab.proof

open LeanModels LeanModels.Python

load_program divmod_lab from "Examples/python/divmod_lab/divmod_lab.json"

set_option maxRecDepth 8192

#py_check divmod_lab.pair(7, 3) = (Val.tuple #[.int 2, .int 1])
#py_check divmod_lab.pair(-7, 3) = (Val.tuple #[.int (-3), .int 2])
#py_check divmod_lab.pair(7, -3) = (Val.tuple #[.int (-3), .int (-2)])
#py_check divmod_lab.pair(-7, -3) = (Val.tuple #[.int 2, .int (-1)])
#py_check divmod_lab.pair(6, 3) = (Val.tuple #[.int 2, .int 0])
#py_check divmod_lab.pair(-6, 3) = (Val.tuple #[.int (-2), .int 0])
#py_check divmod_lab.pair(6, -3) = (Val.tuple #[.int (-2), .int 0])
#py_check divmod_lab.pair(-6, -3) = (Val.tuple #[.int 2, .int 0])
#py_check divmod_lab.pair(0, -3) = (Val.tuple #[.int 0, .int 0])
#py_check divmod_lab.pair(true, true) = (Val.tuple #[.int 1, .int 0])
#py_check divmod_lab.pair(false, true) = (Val.tuple #[.int 0, .int 0])
#py_check divmod_lab.pair(7, true) = (Val.tuple #[.int 7, .int 0])
#py_check divmod_lab.pair(true, -3) = (Val.tuple #[.int (-1), .int (-2)])
#py_check divmod_lab.generated() =
  (Val.tuple #[.tuple #[.int (-2), .int 2], .tuple #[.int (-1), .int 0],
    .tuple #[.int (-1), .int 1], .tuple #[.int (-1), .int 2],
    .tuple #[.int 0, .int 0], .tuple #[.int 0, .int 1],
    .tuple #[.int 0, .int 2], .tuple #[.int 1, .int 0],
    .tuple #[.int 1, .int 1]])
#py_check divmod_lab.generator_parameter(5) raises
  (.typeError "'int' object is not callable")
#py_check divmod_lab.generator_nested() = (Val.tuple #[.int 77, .int 77])
#py_check divmod_lab.generator_local() raises
  (.typeError "'int' object is not callable")
#py_check divmod_lab.generator_bool(5) raises
  (.typeError "'int' object is not callable")
#py_check divmod_lab.pair(7, 0) raises .zeroDivisionError
#py_check divmod_lab.pair(true, false) raises .zeroDivisionError
#py_check divmod_lab.arity_zero() raises
  (.typeError "divmod expected 2 arguments, got 0")
#py_check divmod_lab.arity_one() raises
  (.typeError "divmod expected 2 arguments, got 1")
#py_check divmod_lab.arity_three() raises
  (.typeError "divmod expected 2 arguments, got 3")
#py_check divmod_lab.shadow(3) = 5
#py_check divmod_lab.exception_before_arity() raises .zeroDivisionError
#py_check divmod_lab.arity_effects() = (Val.list #[.int 0, .int 1, .int 2])

#guard callFunction divmod_lab "pair" #[.str "7", .int 3] 4096 matches .unsupported _
#guard callFunction divmod_lab "pair" #[.int 7, .none] 4096 matches .unsupported _
#guard callFunction divmod_lab "kwargs" #[] 4096 matches .unsupported _
#guard callFunction divmod_lab "first_class" #[] 4096 matches .unsupported _

theorem by_one_total (value : PyInt) :
    divmod_lab.by_one(value) ==> (Val.tuple #[.int value, .int 0]) := by proofs

#print axioms by_one_total

#py_check divmod_lab.pair(Float64.ofBits 0x3ff0000000000000,
    Float64.ofBits 0x3fb999999999999a) =
    (Float64.ofBits 0x4022000000000000, Float64.ofBits 0x3fb9999999999996)

theorem float_pair_tenth :
    divmod_lab.pair(Float64.ofBits 0x3ff0000000000000,
      Float64.ofBits 0x3fb999999999999a) ==>
      (Float64.ofBits 0x4022000000000000, Float64.ofBits 0x3fb9999999999996) := by proofs

#print axioms float_pair_tenth
