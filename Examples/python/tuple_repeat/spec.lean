import Examples.python.tuple_repeat.proof

open LeanModels LeanModels.Python

load_program tuple_repeat from "Examples/python/tuple_repeat/tuple_repeat.json"

set_option maxRecDepth 8192

#py_check tuple_repeat.repeat_right((Val.tuple #[.int 7, .int 8]), 3) =
  (Val.tuple #[.int 7, .int 8, .int 7, .int 8, .int 7, .int 8])
#py_check tuple_repeat.repeat_left(2, (Val.tuple #[.int 7, .int 8])) =
  (Val.tuple #[.int 7, .int 8, .int 7, .int 8])
#py_check tuple_repeat.repeat_aug((Val.tuple #[.int 7, .int 8]), 2) =
  (Val.tuple #[.int 7, .int 8, .int 7, .int 8])
#py_check tuple_repeat.repeat_right((Val.tuple #[.int 7, .int 8]), 0) =
  (Val.tuple #[])
#py_check tuple_repeat.repeat_left(-3, (Val.tuple #[.int 7, .int 8])) =
  (Val.tuple #[])
#py_check tuple_repeat.repeat_aug((Val.tuple #[.int 7, .int 8]), -3) =
  (Val.tuple #[])
#py_check tuple_repeat.repeat_right((Val.tuple #[.int 7, .int 8]), true) =
  (Val.tuple #[.int 7, .int 8])
#py_check tuple_repeat.repeat_left(false, (Val.tuple #[.int 7, .int 8])) =
  (Val.tuple #[])
#py_check tuple_repeat.repeat_empty(3) = (Val.tuple #[])
#py_check tuple_repeat.repeat_empty(-3) = (Val.tuple #[])
#py_check tuple_repeat.repeat_right_length(3) = 6
#py_check tuple_repeat.repeat_left_length(3) = 6
#py_check tuple_repeat.repeat_aug_length(3) = 6
#py_check tuple_repeat.repeat_empty_length(3) = 0
#py_check tuple_repeat.repeat_right((Val.tuple #[.int 7]), -1048577) = (Val.tuple #[])
#py_check tuple_repeat.repeat_left(1048577, (Val.tuple #[])) = (Val.tuple #[])
#py_check tuple_repeat.repeat_left(-1048577, (Val.tuple #[])) = (Val.tuple #[])
#py_check tuple_repeat.repeat_aug((Val.tuple #[]), 1048577) = (Val.tuple #[])
#py_check tuple_repeat.repeat_namedtuple(-1048577) = (Val.tuple #[])
#py_check tuple_repeat.repeat_namedtuple(2) =
  (Val.tuple #[.int 7, .int 8, .int 7, .int 8])
#py_check tuple_repeat.repeat_namedtuple_left(2) =
  (Val.tuple #[.int 7, .int 8, .int 7, .int 8])
#py_check tuple_repeat.repeat_namedtuple_aug(2) =
  (Val.tuple #[.int 7, .int 8, .int 7, .int 8])
#py_check tuple_repeat.repeat_shallow_alias(2) = 9

#py_check tuple_repeat.repeat_right((Val.tuple #[.int 7]), Val.none) raises
  (.typeError "can't multiply sequence by non-int of type 'NoneType'")
#py_check tuple_repeat.repeat_left(Val.none, (Val.tuple #[.int 7])) raises
  (.typeError "can't multiply sequence by non-int of type 'NoneType'")
#py_check tuple_repeat.repeat_right((Val.tuple #[.int 7]), "ab") raises
  (.typeError "can't multiply sequence by non-int of type 'str'")
#py_check tuple_repeat.repeat_left("ab", (Val.tuple #[.int 7])) raises
  (.typeError "can't multiply sequence by non-int of type 'tuple'")

#guard callFunction tuple_repeat "repeat_right" #[.tuple #[.int 7], .int 1048577] 4096
  matches .unsupported _
#guard callFunction tuple_repeat "repeat_aug" #[.tuple #[.int 7], .int 1048577] 4096
  matches .unsupported _
#guard callFunction tuple_repeat "repeat_right_length" #[.int 524289] 4096
  matches .unsupported _
#guard callFunction tuple_repeat "repeat_empty_length" #[.int (-1048577)] 4096 matches .ok (.int 0)
#guard callFunction tuple_repeat "repeat_empty" #[.int 1267650600228229401496703205376] 4096
  matches .exn (.overflowError "cannot fit 'int' into an index-sized integer")

theorem repeat_right_length_total (count : PyInt)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : 2 * count.toNat ≤ 1048576) :
    tuple_repeat.repeat_right_length(count) ==> 2 * (count.toNat : Int) := by proofs

theorem repeat_empty_length_total (count : PyInt)
    (countBound : count.natAbs ≤ 1048576) :
    tuple_repeat.repeat_empty_length(count) ==> (0 : Int) := by proofs

#print axioms repeat_right_length_total
#print axioms repeat_empty_length_total
