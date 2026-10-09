import LeanModels.Python.Surface
import LeanModels.Python.Delab

namespace Examples.python.string_repeat.proof

open LeanModels LeanModels.Python

load_program string_repeat from "Examples/python/string_repeat/string_repeat.json"

private theorem tripled_ab : strRepeat "ab" 3 = .ok (.str "ababab") := by
  rfl

private theorem tripled_ab_length : lenVal (.str "ababab") = .ok (.int 6) := by
  rfl

theorem repeat_right_total (text : PyStr) (count : PyInt)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : text.length * count.toNat ≤ 1048576) :
    string_repeat.repeat_right(text, count) ==>
      String.ofList ((List.replicate count.toNat text.toList).flatten) := by
  py_prove [string_repeat, sequenceMult, sequenceRepeat, strRepeat, seqBudget,
    countBound, outputBound]

theorem repeat_left_total (text : PyStr) (count : PyInt)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : text.length * count.toNat ≤ 1048576) :
    string_repeat.repeat_left(count, text) ==>
      String.ofList ((List.replicate count.toNat text.toList).flatten) := by
  py_prove [string_repeat, sequenceMult, sequenceRepeat, strRepeat, seqBudget,
    countBound, outputBound]

theorem decorated_total (text : PyStr) (count : PyInt)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : text.length * count.toNat ≤ 1048576) :
    string_repeat.decorated(text, count) ==>
      ("[" ++ String.ofList ((List.replicate count.toNat text.toList).flatten) ++ "]") := by
  py_prove [string_repeat, sequenceMult, sequenceRepeat, strRepeat, seqBudget,
    countBound, outputBound]

theorem width_offset_total (offset : PyInt) :
    string_repeat.width_offset(offset) ==> 6 + offset := by
  py_prove [string_repeat, sequenceMult, sequenceRepeat, tripled_ab,
    tripled_ab_length]
  rfl

end Examples.python.string_repeat.proof
