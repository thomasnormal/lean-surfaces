import LeanModels.Python.Surface

namespace Examples.python.exc_handlers_lab.proof

open LeanModels LeanModels.Python

load_program exc_handlers_lab from "Examples/python/exc_handlers_lab/exc_handlers_lab.json"

private theorem floorDiv_ne_bitAnd :
    (BinOp.floorDiv == BinOp.bitAnd) = false := by
  decide

private theorem len_ne_lenMult :
    ("len" == lenMultBuiltinName) = false := by
  decide

theorem caught_type_identity_total (value : PyInt) :
    exc_handlers_lab.caught_type_identity(value) ==> value := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [exc_handlers_lab, excHandlerNames, excHandlerTuple,
    excHandlerAdmitted, excHandlerMatches, floorDiv_ne_bitAnd,
    len_ne_lenMult, lenMultBuiltinName]

theorem tuple_handler :
    exc_handlers_lab.tuple_handler() ==> (13 : PyInt) := by
  refine ⟨64, ?_⟩
  unfold callFunction
  rw [callIn.eq_2]
  py_simp [exc_handlers_lab, excHandlerNames, excHandlerTuple,
    excHandlerAdmitted, excHandlerMatches, floorDiv_ne_bitAnd,
    len_ne_lenMult, lenMultBuiltinName]

#print axioms caught_type_identity_total

end Examples.python.exc_handlers_lab.proof
