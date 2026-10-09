import Examples.python.string_repeat.proof

open LeanModels LeanModels.Python

load_program string_repeat from "Examples/python/string_repeat/string_repeat.json"

set_option maxRecDepth 8192

#py_check string_repeat.repeat_right("ab", 3) = "ababab"
#py_check string_repeat.repeat_left(3, "ab") = "ababab"
#py_check string_repeat.repeat_right("ab", 0) = ""
#py_check string_repeat.repeat_left(-3, "ab") = ""
#py_check string_repeat.repeat_right("", 3) = ""
#py_check string_repeat.repeat_left(3, "") = ""
#py_check string_repeat.repeat_right("ab", true) = "ab"
#py_check string_repeat.repeat_right("ab", false) = ""
#py_check string_repeat.repeat_left(true, "ab") = "ab"
#py_check string_repeat.repeat_left(false, "ab") = ""
#py_check string_repeat.repeat_right("λ😀", 2) = "λ😀λ😀"
#py_check string_repeat.repeat_left(2, "a\u0000b") = "a\u0000ba\u0000b"
#py_check string_repeat.repeat_aug("xy", 3) = "xyxyxy"
#py_check string_repeat.repeat_aug("xy", -2) = ""
#py_check string_repeat.repeat_aug("λ", true) = "λ"
#py_check string_repeat.repeat_right_length("λ😀", 3) = 6
#py_check string_repeat.repeat_left_length(3, "ab") = 6
#py_check string_repeat.repeat_aug_length("xy", 3) = 6
#py_check string_repeat.decorated("ab", 2) = "[abab]"
#py_check string_repeat.decorated("ab", -1) = "[]"
#py_check string_repeat.width_offset(-7) = -1

#py_check string_repeat.repeat_right("ab", Val.none) raises
  (.typeError "can't multiply sequence by non-int of type 'NoneType'")
#py_check string_repeat.repeat_left(Val.none, "ab") raises
  (.typeError "can't multiply sequence by non-int of type 'NoneType'")
#py_check string_repeat.repeat_right("ab", "xy") raises
  (.typeError "can't multiply sequence by non-int of type 'str'")
#py_check string_repeat.repeat_left("xy", "ab") raises
  (.typeError "can't multiply sequence by non-int of type 'str'")
#py_check string_repeat.repeat_right("ab", (Val.tuple #[.int 1])) raises
  (.typeError "can't multiply sequence by non-int of type 'tuple'")
#py_check string_repeat.repeat_left((Val.tuple #[.int 1]), "ab") raises
  (.typeError "can't multiply sequence by non-int of type 'str'")
#py_check string_repeat.repeat_aug("ab", Val.none) raises
  (.typeError "can't multiply sequence by non-int of type 'NoneType'")
#py_check string_repeat.repeat_right((Val.list #[.int 1]), (Val.tuple #[.int 1])) raises
  (.typeError "can't multiply sequence by non-int of type 'tuple'")
#py_check string_repeat.repeat_left((Val.list #[.int 1]), (Val.tuple #[.int 1])) raises
  (.typeError "can't multiply sequence by non-int of type 'tuple'")
#guard callFunction string_repeat "repeat_aug"
  #[.list #[.int 1], .tuple #[.int 1]] 4096 matches .unsupported _

#guard callFunction string_repeat "repeat_right" #[.str "ab", .int 1048577] 4096
  matches .unsupported _
#guard callFunction string_repeat "repeat_right" #[.str "ab", .int (-1048577)] 4096
  matches .unsupported _
#guard callFunction string_repeat "repeat_left" #[.int 1048577, .str ""] 4096
  matches .unsupported _
#guard callFunction string_repeat "repeat_left" #[.int (-1048577), .str ""] 4096
  matches .unsupported _
#guard callFunction string_repeat "repeat_right" #[.str "ab", .int 1048576] 4096
  matches .unsupported _
#guard callFunction string_repeat "repeat_right"
  #[.str (String.ofList (List.replicate 1025 'x')), .int 1024] 4096
  matches .unsupported _
#guard callFunction string_repeat "repeat_live_list" #[.int 2] 4096
  matches .unsupported _

theorem repeat_right_total (text : PyStr) (count : PyInt)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : text.length * count.toNat ≤ 1048576) :
    string_repeat.repeat_right(text, count) ==>
      String.ofList ((List.replicate count.toNat text.toList).flatten) := by proofs

theorem repeat_left_total (text : PyStr) (count : PyInt)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : text.length * count.toNat ≤ 1048576) :
    string_repeat.repeat_left(count, text) ==>
      String.ofList ((List.replicate count.toNat text.toList).flatten) := by proofs

theorem decorated_total (text : PyStr) (count : PyInt)
    (countBound : count.natAbs ≤ 1048576)
    (outputBound : text.length * count.toNat ≤ 1048576) :
    string_repeat.decorated(text, count) ==>
      "[" ++ String.ofList ((List.replicate count.toNat text.toList).flatten) ++ "]" := by proofs

theorem width_offset_total (offset : PyInt) :
    string_repeat.width_offset(offset) ==> 6 + offset := by proofs
