import LeanModels.Python

namespace Examples.python.sum_order_lab.proof

open LeanModels LeanModels.Python

load_program sum_order_lab from "Examples/python/sum_order_lab/sum_order_lab.json"

theorem int_before_string_start (value : PyInt) (start : PyStr) :
    sum_order_lab.rejected_start(value, start) ==>!
      (.typeError "'int' object is not iterable") := by
  exact ⟨64, rfl⟩

theorem int_before_bytes_start (value : PyInt) (start : PyBytes) :
    sum_order_lab.rejected_start(value, start) ==>!
      (.typeError "'int' object is not iterable") := by
  exact ⟨64, rfl⟩

theorem string_start_preserves_generator (start : PyStr) :
    sum_order_lab.generator_untouched(start) ==> (7 : PyInt) := by
  exact CallsTo.intro 64 (by rfl)

theorem bytes_start_preserves_generator (start : PyBytes) :
    sum_order_lab.generator_untouched(start) ==> (7 : PyInt) := by
  exact CallsTo.intro 64 (by rfl)

#print axioms int_before_string_start
#print axioms int_before_bytes_start
#print axioms string_start_preserves_generator
#print axioms bytes_start_preserves_generator

end Examples.python.sum_order_lab.proof
