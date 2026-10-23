import Examples.python.repr_lab.proof
import LeanModels.Python.Script

open LeanModels LeanModels.Python

load_program repr_lab from "Examples/python/repr_lab/repr_lab.json"
load_program repr_shadow from "Examples/python/repr_lab/repr_shadow.json"
load_program repr_script from "Examples/python/repr_lab/repr_script.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 1024

#py_check repr_lab.of(0) = "0"
#py_check repr_lab.of(-17) = "-17"
#py_check repr_lab.of(true) = "True"
#py_check repr_lab.of(false) = "False"
#py_check repr_lab.of(Val.none) = "None"
#py_check repr_lab.of("") = "''"
#py_check repr_lab.of("quoted") = "'quoted'"
#py_check repr_lab.of("a'b") = "\"a'b\""
#py_check repr_lab.of("a\"b") = "'a\"b'"
#py_check repr_lab.of("\n\r\t") = "'\\n\\r\\t'"
#py_check repr_lab.of("\x00\x7f") = "'\\x00\\x7f'"
#py_check repr_lab.of(Val.list #[.str "x"]) = "['x']"
#py_check repr_lab.of(Val.tuple #[.int 1]) = "(1,)"
#py_check repr_lab.containers() = "([], [1, 'x'], {'x': [None, True]}, (1,), ())"
#py_check repr_lab.named() = "Pair(left='x', right=[1, 2])"
#py_check repr_lab.ranges() = "(range(0, True), range(False, 3), range(5, 0, -2))"
#py_check repr_lab.recursive_list() = "[[...]]"
#py_check repr_lab.recursive_dict() = "{'self': {...}}"
#py_check repr_lab.shared_path() = "([1], [1])"
#py_check repr_lab.updated_argument() = "(None, [1])"
#py_check repr_lab.no_arguments() raises
  .typeError "repr() takes exactly one argument (0 given)"
#py_check repr_lab.two_arguments() raises
  .typeError "repr() takes exactly one argument (2 given)"
#py_check repr_lab.arity_effects() = (Val.list #[.int 1, .int 2, .int 3])
#py_check repr_lab.argument_failure() raises .zeroDivisionError
#py_check repr_lab.excess_argument_failure() raises .zeroDivisionError
#py_check repr_lab.local_shadow() = 10
#py_check repr_lab.parameter_shadow(1) raises .typeError "'int' object is not callable"
#py_check repr_lab.generator_shadow() = (Val.tuple #[.int 8, .int 9])
#py_check repr_shadow.direct(-7) = 4
#py_check repr_shadow.captured_generator() = (Val.tuple #[.int 12, .int 13])

#guard callFunction repr_lab "of" #[.str "é"] 4096 matches .unsupported _
#py_check repr_lab.keyword() raises
  .typeError "repr() takes no keyword arguments"
#guard callFunction repr_lab "first_class" #[] 4096 matches .unsupported _
#guard callFunction repr_lab "instance" #[] 4096 matches .unsupported _
#guard callFunction repr_lab "custom" #[] 4096 matches .unsupported _
#guard callFunction repr_lab "set_value" #[] 4096 matches .unsupported _
#guard callFunction repr_lab "closure" #[] 4096 matches .unsupported _
#guard callFunction repr_lab "generator" #[] 4096 matches .unsupported _
#guard callFunction repr_lab "large_length" #[.int 1025] 4096 matches .unsupported _
#guard callFunction repr_lab "deep" #[.int 65] 4096 matches .ok _
#guard callFunction repr_lab "deep" #[.int 80] 4096 matches .ok _
#guard callFunction repr_lab "deep" #[.int 129] 4096 matches .unsupported _
#guard callFunction repr_lab "of" #[.bool true] 1 matches .timeout

#guard match runScript repr_script 4096 with
  | .ok world () => world.stdout ==
      ["'quoted'", "[1, 'x', None]", "[[...]]", "first", "second",
       "arity after arguments", "before error", "argument error before arity"]
  | _ => false

theorem boolean_repr (value : PyBool) :
    repr_lab.of(value) ==> (if value then "True" else "False") := by proofs

theorem integer_repr (value : PyInt) (valueBound : value.natAbs < 10 ^ 1024) :
    repr_lab.of(value) ==> toString value := by proofs

#print axioms boolean_repr
#print axioms integer_repr
