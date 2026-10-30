import Examples.python.exc_handlers_lab.proof
import LeanModels.Python.Script

open LeanModels LeanModels.Python

load_program exc_handlers_lab from "Examples/python/exc_handlers_lab/exc_handlers_lab.json"
load_program exc_handlers_script from "Examples/python/exc_handlers_lab/exc_handlers_script.json"
load_program exc_handlers_rebound_script from "Examples/python/exc_handlers_lab/exc_handlers_rebound_script.json"

set_option maxRecDepth 8192

#py_check exc_handlers_lab.caught_type_identity(0) = 0
#py_check exc_handlers_lab.caught_type_identity(-7) = -7
#py_check exc_handlers_lab.quotient_or_zero(7, 3) = 2
#py_check exc_handlers_lab.quotient_or_zero(-7, 3) = -3
#py_check exc_handlers_lab.quotient_or_zero(7, 0) = 0
#py_check exc_handlers_lab.power_zero() = 2
#py_check exc_handlers_lab.value_error("12") = 12
#py_check exc_handlers_lab.value_error("bad") = -1
#py_check exc_handlers_lab.index_error(-1) = 8
#py_check exc_handlers_lab.index_error(2) = -1
#py_check exc_handlers_lab.key_error(1) = 10
#py_check exc_handlers_lab.key_error(2) = -1
#py_check exc_handlers_lab.name_error() = 3
#py_check exc_handlers_lab.attribute_error() = 4
#py_check exc_handlers_lab.assertion_error(1) = 5
#py_check exc_handlers_lab.assertion_error(0) = -5
#py_check exc_handlers_lab.stop_iteration() = 6
#py_check exc_handlers_lab.runtime_catches_recursion() = 7
#py_check exc_handlers_lab.recursion_exact() = 8
#py_check exc_handlers_lab.exception_user() = 9
#py_check exc_handlers_lab.exception_builtin() = 10
#py_check exc_handlers_lab.nonmatching_builtin() raises .zeroDivisionError
#guard callFunction exc_handlers_lab "nonmatching_user" #[] 4096
  matches .exn (.user _ "Signal")
#py_check exc_handlers_lab.nested_nonmatching() = (Val.list #[.int 1, .int 3])
#py_check exc_handlers_lab.type_mutation() =
  (Val.list #[.int 7, .int 8, .int 9, .int 10, .int 11])
#py_check exc_handlers_lab.subscript_mutation() = (Val.list #[.int 0, .int 1, .int 3])
#py_check exc_handlers_lab.handler_raises() raises .zeroDivisionError
#py_check exc_handlers_lab.nested_handler_raises() = 12

#guard callFunction exc_handlers_lab "handler_binding" #[] 4096 matches .unsupported _
#py_check exc_handlers_lab.tuple_handler() = 13
#guard callFunction exc_handlers_lab "shadowed_handler" #[.int 5] 4096 matches
  .exn (.typeError "catching classes that do not inherit from BaseException is not allowed")
#guard callFunction exc_handlers_lab "local_shadowed_handler" #[] 4096 matches .ok (.int 1)
#guard callFunction exc_handlers_lab "body_shadowed_handler" #[] 4096 matches
  .exn (.typeError "catching classes that do not inherit from BaseException is not allowed")
#guard callFunction exc_handlers_lab "body_shadowed_nonmatching" #[] 4096 matches
  .exn (.typeError "catching classes that do not inherit from BaseException is not allowed")
#guard callFunction exc_handlers_lab "late_shadowed_handler" #[] 4096 matches
  .exn (.unboundLocalError "TypeError")
#guard callFunction exc_handlers_lab "nested_def_handler" #[] 4096 matches
  .exn (.typeError "catching classes that do not inherit from BaseException is not allowed")
#py_check exc_handlers_lab.base_exception() = 16
#py_check exc_handlers_lab.arithmetic_ancestor() = 17
#py_check exc_handlers_lab.lookup_ancestor() = 18
#py_check exc_handlers_lab.else_clause() = 1
#py_check exc_handlers_lab.finally_clause() = (Val.list #[.int 19])
#py_check exc_handlers_lab.multiple_handlers() = 21
#py_check exc_handlers_lab.bare_handler() = 22
#guard callFunction exc_handlers_lab "exception_value" #[] 4096 matches .unsupported _
#py_check exc_handlers_lab.loud_body() = Float64.ofBits 0x3ff0000000000000
#guard callFunction exc_handlers_lab "caught_type_identity" #[.int 7] 3 matches .timeout

#guard match runScript exc_handlers_script 4096 with
  | .ok world () => world.stdout == ["3", "[0, 1, 2]"]
  | _ => false

#guard match runScript exc_handlers_rebound_script 4096 with
  | .exn _ (.typeError msg) => msg == "catching classes that do not inherit from BaseException is not allowed"
  | _ => false

theorem caught_type_identity_total (value : PyInt) :
    exc_handlers_lab.caught_type_identity(value) ==> value := by proofs

#print axioms caught_type_identity_total
