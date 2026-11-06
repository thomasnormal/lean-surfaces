import LeanModels.Python.Surface
import LeanModels.Python.Delab

namespace Examples.python.tuple_repeat.proof

open LeanModels LeanModels.Python

load_program tuple_repeat from "Examples/python/tuple_repeat/tuple_repeat.json"

theorem repeat_right_length_total :
    tuple_repeat.repeat_right_length(3) ==> (6 : Int) := by
  exact ⟨256, rfl⟩

theorem repeat_empty_length_total :
    tuple_repeat.repeat_empty_length(3) ==> (0 : Int) := by
  exact ⟨256, rfl⟩

#print axioms repeat_right_length_total
#print axioms repeat_empty_length_total

end Examples.python.tuple_repeat.proof
