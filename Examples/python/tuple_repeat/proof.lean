import LeanModels.Python.Surface
import LeanModels.Python.Delab

namespace Examples.python.tuple_repeat.proof

open LeanModels LeanModels.Python

load_program tuple_repeat from "Examples/python/tuple_repeat/tuple_repeat.json"

private theorem repeatedTuple_size (values : Array RVal) (count : Nat) :
    ((List.replicate count values.toList).flatten.toArray).size = values.size * count := by
  simp [List.sum_replicate_nat, Nat.mul_comm]

theorem repeat_right_length_total (count : PyInt)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : 2 * count.toNat ≤ 1048576) :
    tuple_repeat.repeat_right_length(count) ==> 2 * (count.toNat : Int) := by
  have indexBound : ¬count.natAbs > seqIndexBudget := by
    simp only [seqIndexBudget]
    omega
  by_cases nonpositive : count ≤ 0
  · have zeroCount : count.toNat = 0 := Int.toNat_eq_zero.mpr nonpositive
    py_prove [tuple_repeat, sequenceMult, sequenceRepeat, tupleRepeat,
      indexBound, nonpositive, zeroCount]
  · py_prove [tuple_repeat, sequenceMult, sequenceRepeat, tupleRepeat, seqBudget,
      indexBound, nonpositive, countBound, outputBound, repeatedTuple_size]

theorem repeat_empty_length_total (count : PyInt)
    (countBound : count.natAbs ≤ 1048576) :
    tuple_repeat.repeat_empty_length(count) ==> (0 : Int) := by
  have indexBound : ¬count.natAbs > seqIndexBudget := by
    simp only [seqIndexBudget]
    omega
  py_prove [tuple_repeat, sequenceMult, sequenceRepeat, tupleRepeat, seqBudget,
    indexBound, countBound, repeatedTuple_size]

#print axioms repeat_right_length_total
#print axioms repeat_empty_length_total

end Examples.python.tuple_repeat.proof
