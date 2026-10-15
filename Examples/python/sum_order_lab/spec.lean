import Examples.python.sum_order_lab.proof

open LeanModels LeanModels.Python

load_program sum_order_lab from "Examples/python/sum_order_lab/sum_order_lab.json"

#py_check sum_order_lab.rejected_start(1, "") raises
  (.typeError "'int' object is not iterable")
#py_check sum_order_lab.rejected_start(Val.none, "") raises
  (.typeError "'NoneType' object is not iterable")
#py_check sum_order_lab.rejected_start(true, "x") raises
  (.typeError "'bool' object is not iterable")
#py_check sum_order_lab.rejected_start(Float64.ofBits 0x4004000000000000, "") raises
  (.typeError "'float' object is not iterable")
#py_check sum_order_lab.rejected_start(Val.ellipsis, Val.bytes #[]) raises
  (.typeError "'ellipsis' object is not iterable")
#py_check sum_order_lab.rejected_start(Val.list #[], "") raises
  (.typeError "sum() can't sum strings [use ''.join(seq) instead]")
#py_check sum_order_lab.rejected_start(Val.tuple #[], Val.bytes #[]) raises
  (.typeError "sum() can't sum bytes [use b''.join(seq) instead]")
#py_check sum_order_lab.dict_start("") raises
  (.typeError "sum() can't sum strings [use ''.join(seq) instead]")
#py_check sum_order_lab.set_start(Val.bytes #[]) raises
  (.typeError "sum() can't sum bytes [use b''.join(seq) instead]")
#py_check sum_order_lab.list_start("") raises
  (.typeError "sum() can't sum strings [use ''.join(seq) instead]")
#py_check sum_order_lab.range_start("") raises
  (.typeError "sum() can't sum strings [use ''.join(seq) instead]")
#py_check sum_order_lab.range_start(Val.bytes #[]) raises
  (.typeError "sum() can't sum bytes [use b''.join(seq) instead]")
#py_check sum_order_lab.namedtuple_start("") raises
  (.typeError "sum() can't sum strings [use ''.join(seq) instead]")
#py_check sum_order_lab.function_start("") raises
  (.typeError "'function' object is not iterable")
#py_check sum_order_lab.function_start(Val.bytes #[]) raises
  (.typeError "'function' object is not iterable")
#py_check sum_order_lab.instance_start("") raises
  (.typeError "'Plain' object is not iterable")
#py_check sum_order_lab.instance_start(Val.bytes #[]) raises
  (.typeError "'Plain' object is not iterable")
#py_check sum_order_lab.generator_start("") raises
  (.typeError "sum() can't sum strings [use ''.join(seq) instead]")
#py_check sum_order_lab.generator_start(Val.bytes #[]) raises
  (.typeError "sum() can't sum bytes [use b''.join(seq) instead]")
#py_check sum_order_lab.generator_untouched("") = 7
#py_check sum_order_lab.generator_untouched(Val.bytes #[]) = 7
#py_check sum_order_lab.enumerate_untouched("") = Val.tuple #[.int 0, .int 5]
#py_check sum_order_lab.arguments_evaluated("") = Val.tuple #[.int 1, .int 2]
#py_check sum_order_lab.element_evaluated("") raises .zeroDivisionError

#guard (sumRejectedStart sum_order_lab #[] (.ref 0) "start" matches .unsupported _)
#guard (sumRejectedStart sum_order_lab #[.cell none] (.ref 0) "start" matches .unsupported _)
#guard (sumRejectedStart sum_order_lab #[.instance 99 #[]] (.ref 0) "start"
  matches .unsupported _)

theorem int_before_string_start (value : PyInt) (start : PyStr) :
    sum_order_lab.rejected_start(value, start) ==>!
      (.typeError "'int' object is not iterable") := by proofs

theorem int_before_bytes_start (value : PyInt) (start : PyBytes) :
    sum_order_lab.rejected_start(value, start) ==>!
      (.typeError "'int' object is not iterable") := by proofs

theorem string_start_preserves_generator (start : PyStr) :
    sum_order_lab.generator_untouched(start) ==> (7 : PyInt) := by proofs

theorem bytes_start_preserves_generator (start : PyBytes) :
    sum_order_lab.generator_untouched(start) ==> (7 : PyInt) := by proofs
