import LeanModels.Python.Surface
import LeanModels.Python.Delab

namespace Examples.python.string_repeat.proof

open LeanModels LeanModels.Python

load_program string_repeat from "Examples/python/string_repeat/string_repeat.json"

private theorem tripled_ab : strRepeat "ab" 3 = .ok (.str "ababab") := by
  rfl

private theorem tripled_ab_length : lenVal (.str "ababab") = .ok (.int 6) := by
  rfl

private theorem mult_ne_bitAnd : (BinOp.mult == BinOp.bitAnd) = false := by
  decide

private theorem add_ne_bitAnd : (BinOp.add == BinOp.bitAnd) = false := by
  decide

private theorem strRepeat_of_bounds (text : String) (count : Int)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : text.length * count.toNat ≤ 1048576) :
    strRepeat text count =
      .ok (.str (String.ofList ((List.replicate count.toNat text.toList).flatten))) := by
  have indexBound : ¬count.natAbs > seqIndexBudget := by
    simp only [seqIndexBudget]
    omega
  by_cases nonpositive : count ≤ 0
  · have zeroCount : count.toNat = 0 := Int.toNat_eq_zero.mpr nonpositive
    simp [strRepeat, indexBound, nonpositive, zeroCount]
  · by_cases empty : text = ""
    · subst text
      simp [strRepeat, indexBound]
    · have nonempty : text.isEmpty = false := String.isEmpty_eq_false_iff.mpr empty
      simp [strRepeat, indexBound, nonpositive, nonempty, seqBudget, countBound, outputBound]

theorem repeat_right_total (text : PyStr) (count : PyInt)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : text.length * count.toNat ≤ 1048576) :
    string_repeat.repeat_right(text, count) ==>
      String.ofList ((List.replicate count.toNat text.toList).flatten) := by
  py_prove [string_repeat, lowerLenRepeatPairs, sequenceMult, sequenceMultLength, lenMultBuiltinName, sequenceRepeat, mult_ne_bitAnd, add_ne_bitAnd,
    strRepeat_of_bounds text count countBound outputBound]

theorem repeat_left_total (text : PyStr) (count : PyInt)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : text.length * count.toNat ≤ 1048576) :
    string_repeat.repeat_left(count, text) ==>
      String.ofList ((List.replicate count.toNat text.toList).flatten) := by
  py_prove [string_repeat, lowerLenRepeatPairs, sequenceMult, sequenceMultLength, lenMultBuiltinName, sequenceRepeat, mult_ne_bitAnd, add_ne_bitAnd,
    strRepeat_of_bounds text count countBound outputBound]

theorem decorated_total (text : PyStr) (count : PyInt)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : text.length * count.toNat ≤ 1048576) :
    string_repeat.decorated(text, count) ==>
      ("[" ++ String.ofList ((List.replicate count.toNat text.toList).flatten) ++ "]") := by
  py_prove [string_repeat, lowerLenRepeatPairs, sequenceMult, sequenceMultLength, lenMultBuiltinName, sequenceRepeat, mult_ne_bitAnd, add_ne_bitAnd,
    strRepeat_of_bounds text count countBound outputBound]

theorem width_offset_total (offset : PyInt) :
    string_repeat.width_offset(offset) ==> 6 + offset := by
  py_prove [string_repeat, lowerLenRepeatPairs, sequenceMult, sequenceMultLength, seqIndexBudget, lenMultBuiltinName, sequenceRepeat, mult_ne_bitAnd, add_ne_bitAnd, tripled_ab,
    tripled_ab_length]
  decide

end Examples.python.string_repeat.proof
