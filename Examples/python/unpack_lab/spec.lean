import LeanModels.Python.Surface
open LeanModels LeanModels.Python
load_program unpack_lab from "Examples/python/unpack_lab/unpack_lab.json"
#py_check unpack_lab.tail(Val.tuple #[.int 1, .int 2, .int 3]) =
  (Val.tuple #[.int 1, .list #[.int 2, .int 3]])
#py_check unpack_lab.tail(Val.tuple #[.int 1]) =
  (Val.tuple #[.int 1, .list #[]])
#py_check unpack_lab.head(Val.tuple #[.int 1, .int 2, .int 3]) =
  (Val.tuple #[.list #[.int 1, .int 2], .int 3])
#py_check unpack_lab.middle(Val.tuple #[.int 1, .int 2, .int 3, .int 4]) =
  (Val.tuple #[.int 1, .list #[.int 2, .int 3], .int 4])
#py_check unpack_lab.empty_middle(Val.tuple #[.int 1, .int 2]) =
  (Val.tuple #[.int 1, .list #[], .int 2])
#py_check unpack_lab.from_string() =
  (Val.tuple #[.str "a", .list #[.str "b", .str "c"]])
#py_check unpack_lab.from_range() =
  (Val.tuple #[.int 0, .list #[.int 1, .int 2, .int 3]])
#py_check unpack_lab.too_short(Val.tuple #[.int 1]) raises
  (.valueError "not enough values to unpack (expected at least 2, got 1)")
#py_check unpack_lab.noniterable() raises
  (.typeError "cannot unpack non-iterable int object")
