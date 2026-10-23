import LeanModels.Python

open LeanModels LeanModels.Python

load_program bytes_lab from "Examples/python/bytes_lab/bytes_lab.json"

#py_check bytes_lab.literal() = (#[97, 98, 0, 255] : PyBytes)
#py_check bytes_lab.length() = 4
#py_check bytes_lab.indexing() = Val.tuple #[.int 97, .int 255, .int 98]
#py_check bytes_lab.rendering() =
  Val.tuple #[.str "b'a\\n\\xff'", .str "b'a\\n\\xff'", .str "b'a\\n\\xff'"]
#py_check bytes_lab.concat_repeat() =
  Val.tuple #[Val.bytes #[97, 98, 99], Val.bytes #[97, 98, 97, 98], Val.bytes #[120, 120]]
#py_check bytes_lab.slicing() = Val.bytes #[98, 100]
#py_check bytes_lab.equality_order() = Val.tuple #[.bool true, .bool true, .bool true]
#py_check bytes_lab.iterate() = Val.tuple #[.int 97, .int 98]
#py_check bytes_lab.index_oob() raises (.indexErrorBytes)

#py_check bytes_lab.contains(Val.bytes #[97, 98], Val.bytes #[98]) = true
#py_check bytes_lab.contains(Val.bytes #[97, 98], 256) raises
  (.valueError "byte must be in range(0, 256)")
#py_check bytes_lab.loop(Val.bytes #[97, 98]) = 195
#py_check bytes_lab.tuple_keys(Val.bytes #[0, 128, 255]) = 7
#py_check bytes_lab.sum_start() raises
  (.typeError "sum() can't sum bytes [use b''.join(seq) instead]")
#py_check bytes_lab.sum_start_noniterable() raises
  (.typeError "'int' object is not iterable")
#py_check bytes_lab.sum_start_lazy() raises
  (.typeError "sum() can't sum bytes [use b''.join(seq) instead]")
#py_check bytes_lab.numeric_int() = Val.tuple #[.int 12, .int 0, .int 7]
#py_check bytes_lab.numeric_int_invalid() raises
  (.valueError "invalid literal for int() with base 10: b'12x'")
#py_check bytes_lab.numeric_int_nonascii() raises
  (.valueError "invalid literal for int() with base 10: b'\\xff'")
#py_check bytes_lab.numeric_float() =
  Val.tuple #[.float (Float64.ofBits 0x3ff8000000000000),
    .float (Float64.ofBits 0x4028000000000000)]
#py_check bytes_lab.numeric_float_invalid() raises
  (.valueError "could not convert string to float: b'12x'")
#py_check bytes_lab.numeric_float_nan() =
  Val.tuple #[.float (Float64.ofBits 0x7ff8000000000000),
    .float (Float64.ofBits 0xfff8000000000000),
    .float (Float64.ofBits 0x7ff8000000000000)]
theorem literal : bytes_lab.literal() ==> (#[97, 98, 0, 255] : PyBytes) := by
  exact CallsTo.intro 64 (by rfl)

#print axioms literal

theorem identity (values : PyBytes) : bytes_lab.identity(values) ==> values := by
  exact CallsTo.intro 64 (by rfl)

#print axioms identity
