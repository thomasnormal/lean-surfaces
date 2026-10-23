import Examples.python.fstring_repr.proof
import LeanModels.Python.Script

open LeanModels LeanModels.Python

load_program fstring_repr from "Examples/python/fstring_repr/fstring_repr.json"
load_program fstring_shadow from "Examples/python/fstring_repr/fstring_shadow.json"
load_program fstring_script from "Examples/python/fstring_repr/fstring_script.json"

set_option maxRecDepth 8192
set_option exponentiation.threshold 4300

#py_check fstring_repr.repr_field(true) = "[True]"
#py_check fstring_repr.repr_field(false) = "[False]"
#py_check fstring_repr.repr_field(-17) = "[-17]"
#py_check fstring_repr.repr_field(Val.none) = "[None]"
#py_check fstring_repr.repr_field("quoted") = "['quoted']"
#py_check fstring_repr.repr_field("a'b") = "[\"a'b\"]"
#py_check fstring_repr.repr_field("é") = "['é']"
#py_check fstring_repr.repr_field("\n\r\t") = "['\\n\\r\\t']"
#py_check fstring_repr.repr_field("\x00\x7f") = "['\\x00\\x7f']"
#py_check fstring_repr.str_field("héllo") = "[héllo]"
#py_check fstring_repr.bare_field("héllo") = "[héllo]"
#py_check fstring_repr.mixed("quoted") = "quoted|'quoted'"
#py_check fstring_repr.debug("quoted") = "value='quoted'"
#py_check fstring_repr.empty_spec("quoted") = "'quoted'"
#py_check fstring_repr.empty_bare_spec("quoted") = "quoted"
#py_check fstring_repr.effects() =
    (Val.tuple #[.str "None:[1]:None:[1, 2]", .list #[.int 1, .int 2]])
#py_check fstring_repr.argument_error() = (Val.list #[.int 1])
#py_check fstring_repr.cyclic() = "[[...]]"
#py_check fstring_repr.named() = "Pair(left='x', right=[1, 2])"
#py_check fstring_repr.local_shadow(3) = "3/3/3/value=3"
#py_check fstring_repr.parameter_shadow(7, 8) = "True:False"
#py_check fstring_repr.captured_generator() = (Val.tuple #[.str "1:1", .str "2:2"])
#py_check fstring_shadow.fields(3) = "3/3/3"
#py_check fstring_shadow.captured() = (Val.tuple #[.str "1:1", .str "2:2"])

#guard callFunction fstring_repr "repr_field" #[.str "😀"] 4096 matches .unsupported _
#guard callFunction fstring_repr "instance" #[] 4096 matches .unsupported _
#guard callFunction fstring_repr "repr_field" #[.bool true] 1 matches .timeout
#guard (Expr.formattedValue (.constant (.bool true) default) true default).heapFree

#guard match runScript fstring_script 4096 with
  | .ok world () => world.stdout ==
      ["'x'/None/True", "str=7/repr=8", "shadowed str call", "None:[1]:None:[1, 2]", "[1, 2, [...]]",
       "first", "field error before later field", "'quoted'"]
  | _ => false

theorem boolean_field (value : PyBool) :
    fstring_repr.repr_field(value) ==> ("[" ++ (if value then "True" else "False") ++ "]") := by proofs

theorem integer_field (value : PyInt) (valueBound : value.natAbs < 10 ^ 4300) :
    fstring_repr.repr_field(value) ==> ("[" ++ toString value ++ "]") := by proofs

theorem unicode_str_field (value : PyStr) :
    fstring_repr.str_field(value) ==> ("[" ++ value ++ "]") := by proofs

#print axioms boolean_field
#print axioms integer_field
#print axioms unicode_str_field
