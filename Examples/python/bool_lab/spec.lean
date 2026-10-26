import Examples.python.bool_lab.proof

open LeanModels LeanModels.Python

load_program bool_lab from "Examples/python/bool_lab/bool_lab.json"

set_option maxRecDepth 8192

#py_check bool_lab.zero() = false
#py_check bool_lab.of(0) = false
#py_check bool_lab.of(1) = true
#py_check bool_lab.of(-1) = true
#py_check bool_lab.of(false) = false
#py_check bool_lab.of(true) = true
#py_check bool_lab.of(Val.none) = false
#py_check bool_lab.of("") = false
#py_check bool_lab.of("0") = true
#py_check bool_lab.of(Val.tuple #[]) = false
#py_check bool_lab.of(Val.tuple #[.int 0]) = true
#py_check bool_lab.of(Val.list #[]) = false
#py_check bool_lab.of(Val.list #[.int 0]) = true
#py_check bool_lab.containers() =
  (Val.tuple #[.bool false, .bool true, .bool false, .bool true,
    .bool true, .bool false, .bool true, .bool true, .bool false])
#py_check bool_lab.instance() = true
#py_check bool_lab.closure() = true
#py_check bool_lab.generator() =
  (Val.tuple #[.bool true, .tuple #[.int 0], .bool true])
#py_check bool_lab.mutation() =
  (Val.tuple #[.bool false, .bool true, .int 1])
#py_check bool_lab.arity_two() raises
  (.typeError "bool expected at most 1 argument, got 2")
#py_check bool_lab.arity_three() raises
  (.typeError "bool expected at most 1 argument, got 3")
#py_check bool_lab.shadow(3) = 5
#py_check bool_lab.custom() = false

#py_check bool_lab.kwargs() raises
  (.typeError "bool() takes no keyword arguments")
#guard callFunction bool_lab "first_class" #[] 4096 matches .unsupported _

theorem integer_truth (value : PyInt) :
    bool_lab.of(value) ==> (value != 0) := by proofs

theorem boolean_identity (value : PyBool) :
    bool_lab.of(value) ==> value := by proofs

#print axioms integer_truth
#print axioms boolean_identity
