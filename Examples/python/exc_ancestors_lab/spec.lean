import Examples.python.exc_ancestors_lab.proof
import LeanModels.Python.Script

open LeanModels LeanModels.Python

load_program exc_ancestors_lab from "Examples/python/exc_ancestors_lab/exc_ancestors_lab.json"
load_program exc_ancestors_namesake from "Examples/python/exc_ancestors_lab/exc_ancestors_namesake.json"
load_program exc_ancestors_script from "Examples/python/exc_ancestors_lab/exc_ancestors_script.json"

set_option maxRecDepth 8192

#py_check exc_ancestors_lab.caught_arithmetic_identity(0) = 0
#py_check exc_ancestors_lab.caught_arithmetic_identity(-7) = -7
#py_check exc_ancestors_lab.base_inventory(0) = 100
#py_check exc_ancestors_lab.base_inventory(1) = 101
#py_check exc_ancestors_lab.base_inventory(2) = 102
#py_check exc_ancestors_lab.base_inventory(3) = 103
#py_check exc_ancestors_lab.base_inventory(4) = 104
#py_check exc_ancestors_lab.base_inventory(5) = 105
#py_check exc_ancestors_lab.base_inventory(6) = 106
#py_check exc_ancestors_lab.base_inventory(7) = 107
#py_check exc_ancestors_lab.base_inventory(8) = 108
#py_check exc_ancestors_lab.base_inventory(9) = 109
#py_check exc_ancestors_lab.base_inventory(10) = 110
#py_check exc_ancestors_lab.base_inventory(11) = 111
#py_check exc_ancestors_lab.base_inventory(12) = 17
#py_check exc_ancestors_lab.arithmetic_quotient(7, 3) = 2
#py_check exc_ancestors_lab.arithmetic_quotient(-7, 3) = -3
#py_check exc_ancestors_lab.arithmetic_quotient(7, 0) = 0
#py_check exc_ancestors_lab.arithmetic_power() = 21
#py_check exc_ancestors_lab.arithmetic_type_nonmatch() raises (.typeError "object of type 'int' has no len()")
#guard callFunction exc_ancestors_lab "arithmetic_user_nonmatch" #[] 4096
  matches .exn (.user _ "Signal")
#py_check exc_ancestors_lab.lookup_index(-1) = 8
#py_check exc_ancestors_lab.lookup_index(2) = -1
#py_check exc_ancestors_lab.lookup_key(1) = 10
#py_check exc_ancestors_lab.lookup_key(2) = -1
#py_check exc_ancestors_lab.lookup_arithmetic_nonmatch() raises .zeroDivisionError
#py_check exc_ancestors_lab.lookup_type_nonmatch() raises (.typeError "object of type 'int' has no len()")
#guard callFunction exc_ancestors_lab "lookup_user_nonmatch" #[] 4096
  matches .exn (.user _ "Signal")
#py_check exc_ancestors_lab.arithmetic_mutation() = (Val.list #[.int 0, .int 1, .int 3])
#py_check exc_ancestors_lab.lookup_mutation() = (Val.list #[.int 0, .int 1, .int 3])
#py_check exc_ancestors_lab.nested_fallthrough() = (Val.list #[.int 0, .int 1, .int 3])
#py_check exc_ancestors_lab.handler_raises() raises .indexError
#py_check exc_ancestors_lab.nested_handler_raises() =
  (Val.list #[.int 0, .int 1, .int 2, .int 3])
#py_check exc_ancestors_namesake.base_user() = 41
#py_check exc_ancestors_namesake.base_builtin() raises (.typeError "object of type 'int' has no len()")
#py_check exc_ancestors_namesake.arithmetic_user() = 43
#py_check exc_ancestors_namesake.arithmetic_builtin() raises .zeroDivisionError
#py_check exc_ancestors_namesake.lookup_user() = 45
#py_check exc_ancestors_namesake.lookup_builtin() raises .indexError

#guard callFunction exc_ancestors_lab "parameter_shadow" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_ancestors_lab "body_shadow" #[] 4096 matches .unsupported _
#guard callFunction exc_ancestors_lab "body_shadow_nonmatch" #[] 4096 matches .unsupported _
#guard callFunction exc_ancestors_lab "late_shadow" #[] 4096 matches .unsupported _
#guard callFunction exc_ancestors_lab "os_ancestor" #[] 4096 matches .unsupported _
#guard callFunction exc_ancestors_lab "environment_ancestor" #[] 4096 matches .unsupported _
#guard callFunction exc_ancestors_lab "first_class_base" #[] 4096 matches .unsupported _
#guard callFunction exc_ancestors_lab "raise_base_instance" #[] 4096 matches .unsupported _
#py_check exc_ancestors_lab.raise_arithmetic_class() raises (.builtinException "ArithmeticError")
#py_check exc_ancestors_lab.loud_body() = Float64.ofBits 0x3ff0000000000000
#guard callFunction exc_ancestors_lab "base_runtime" #[] 4096 matches .unsupported _
#guard callFunction exc_ancestors_lab "system_exit_loud" #[] 4096 matches .unsupported _
#guard callFunction exc_ancestors_lab "keyboard_interrupt_loud" #[] 4096 matches .unsupported _
#guard callFunction exc_ancestors_lab "generator_exit_loud" #[] 4096 matches .unsupported _
#guard callFunction exc_ancestors_lab "caught_arithmetic_identity" #[.int 7] 3 matches .timeout

#guard match runScript exc_ancestors_script 4096 with
  | .ok world () => world.stdout == ["[0, 1, 2, 3, 4]"]
  | _ => false

theorem caught_arithmetic_identity_total (value : PyInt) :
    exc_ancestors_lab.caught_arithmetic_identity(value) ==> value := by proofs

#print axioms caught_arithmetic_identity_total
