import Examples.python.ellipsis_lab.proof
import LeanModels.Python.Script

open LeanModels LeanModels.Python

load_program ellipsis_lab from "Examples/python/ellipsis_lab/ellipsis_lab.json"
load_program ellipsis_script from "Examples/python/ellipsis_lab/ellipsis_script.json"

set_option maxRecDepth 8192

#py_check ellipsis_lab.literal() = Val.ellipsis
#py_check ellipsis_lab.builtin() = Val.ellipsis
#py_check ellipsis_lab.default() = Val.ellipsis
#py_check ellipsis_lab.default(Val.none) = Val.none
#py_check ellipsis_lab.identity(Val.ellipsis) =
    (Val.tuple #[.bool true, .bool false, .bool true, .bool false])
#py_check ellipsis_lab.equal(Val.ellipsis) =
    (Val.tuple #[.bool true, .bool false, .bool true, .bool false])
#py_check ellipsis_lab.rendering() =
    (Val.tuple #[.str "Ellipsis", .str "Ellipsis", .str "Ellipsis|Ellipsis|Ellipsis", .str "Ellipsis/Ellipsis"])
#py_check ellipsis_lab.keys() =
    (Val.tuple #[.int 2, .int 4, .int 5, .bool true, .bool true])
#py_check ellipsis_lab.drain() = (Val.list #[.ellipsis, .ellipsis])
#py_check ellipsis_lab.sum_start() = Val.ellipsis
#py_check ellipsis_lab.sum_bad() raises
    .typeError "unsupported operand type(s) for +: 'ellipsis' and 'int'"
#py_check ellipsis_lab.noniterable() raises .typeError "'ellipsis' object is not iterable"
#py_check ellipsis_lab.nonnumeric() raises
    .typeError "unsupported operand type(s) for +: 'ellipsis' and 'int'"

#guard match runScript ellipsis_script 4096 with
  | .ok world () => world.stdout ==
      ["Ellipsis Ellipsis True", "Ellipsis Ellipsis Ellipsis Ellipsis",
       "True False True True", "{Ellipsis: 2} 2 1 True",
       "[Ellipsis, (Ellipsis,), {(Ellipsis,): Ellipsis}]", "True True False",
       "7 False Ellipsis", "Ellipsis True", "ellipsis is not iterable", "Ellipsis"]
  | _ => false

theorem branch_singleton (value : PyBool) :
    ellipsis_lab.branch(value) ==> (if value then Val.ellipsis else Val.none) := by proofs

theorem integer_identity (value : PyInt) :
    ellipsis_lab.identity(value) ==>
      (Val.tuple #[.bool false, .bool true, .bool false, .bool true]) := by proofs

#print axioms branch_singleton
#print axioms integer_identity
