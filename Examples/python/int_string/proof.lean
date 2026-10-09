import LeanModels.Python.Surface
import LeanModels.Python.Delab

namespace Examples.python.int_string.proof

open LeanModels LeanModels.Python

load_program int_string from "Examples/python/int_string/int_string.json"

private theorem grouped_decimal : intOfStr "1_024" = .ok (.int 1024) := by
  rfl

private theorem signed_decimal : intOfStr " \u000b\u000c-2_048\r\n" = .ok (.int (-2048)) := by
  rfl

theorem grouped_offset_total (offset : PyInt) :
    int_string.grouped_offset(offset) ==> 1024 + offset := by
  py_prove [int_string, grouped_decimal]

theorem signed_adjustment_total (offset : PyInt) :
    int_string.signed_adjustment(offset) ==> offset - 2048 := by
  py_prove [int_string, signed_decimal]

theorem grouped_offset_result (offset result : PyInt)
    (run : int_string.grouped_offset(offset) ⇓ result) : result = 1024 + offset :=
  CallsTo.typed_int_eq run (grouped_offset_total offset)

end Examples.python.int_string.proof
