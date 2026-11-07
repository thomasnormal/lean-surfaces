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
#py_check string_repeat.repeat_right("ab", -1048577) = ""
#py_check string_repeat.repeat_left(1048577, "") = ""
#py_check string_repeat.repeat_left(-1048577, "") = ""
#py_check string_repeat.repeat_right("", 1000000000000000000000000000000) raises
  (.overflowError "cannot fit 'int' into an index-sized integer")
#py_check string_repeat.repeat_right("", -1000000000000000000000000000000) raises
  (.overflowError "cannot fit 'int' into an index-sized integer")
#py_check string_repeat.repeat_right("ab", -1000000000000000000000000000000) raises
  (.overflowError "cannot fit 'int' into an index-sized integer")
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
/-! `repeat_aug` on a boundary list refuses since the boundary augmented-repeat
rewrite was removed (`docs/backlog/python-completeness.md`
§2026-11-05-pycomplete-337), and the oversized `repeat_boundary_list_length`
product refuses since the length-only repetition rewrites were removed
(§2026-11-05-pycomplete-340). The CPython answers these checks pinned are
kept in the `-- was` comments; `harness/cases.json` expects `unsupported`
for these rows. -/

-- was `#py_check string_repeat.repeat_aug((Val.list #[.int 1, .int 2]), 3) = (Val.list #[.int 1, .int 2, .int 1, .int 2, .int 1, .int 2])`
#guard callFunction string_repeat "repeat_aug" #[Val.list #[Val.int 1, Val.int 2], .int 3] 4096 matches
  .unsupported "augmented assignment to a list ('+=' mutates in place, visible through aliases) is outside the v0 tier"
-- was `#py_check string_repeat.repeat_aug((Val.list #[.int 1, .int 2]), -2) = (Val.list #[])`
#guard callFunction string_repeat "repeat_aug" #[Val.list #[Val.int 1, Val.int 2], .int (-2)] 4096 matches
  .unsupported "augmented assignment to a list ('+=' mutates in place, visible through aliases) is outside the v0 tier"
-- was `#py_check string_repeat.repeat_aug((Val.list #[.int 1]), (Val.tuple #[.int 1])) raises (.typeError "can't multiply sequence by non-int of type 'tuple'")`
#guard callFunction string_repeat "repeat_aug" #[Val.list #[Val.int 1], Val.tuple #[Val.int 1]] 4096 matches
  .unsupported "augmented assignment to a list ('+=' mutates in place, visible through aliases) is outside the v0 tier"
#py_check string_repeat.repeat_boundary_list((Val.list #[.int 1, .int 2]), 3) =
  (Val.list #[.int 1, .int 2, .int 1, .int 2, .int 1, .int 2])
#py_check string_repeat.repeat_boundary_list(3, (Val.list #[.int 1, .int 2])) =
  (Val.list #[.int 1, .int 2, .int 1, .int 2, .int 1, .int 2])
-- was `#py_check string_repeat.repeat_boundary_list_length((Val.list #[.int 1, .int 2]), 1048577) = 2097154`
#guard callFunction string_repeat "repeat_boundary_list_length" #[Val.list #[Val.int 1, Val.int 2], .int 1048577] 4096 matches
  .unsupported "list repetition beyond seqBudget is outside the tier (count magnitude or output element count; docs/memory-model.md §list repetition)"
#guard callFunction string_repeat "repeat_right" #[.str "ab", .int 1048577] 4096
  matches .unsupported _
#guard callFunction string_repeat "repeat_right" #[.str "ab", .int 1048576] 4096
  matches .unsupported _
#guard callFunction string_repeat "repeat_right"
  #[.str (String.ofList (List.replicate 1025 'x')), .int 1024] 4096
  matches .unsupported _
#py_check string_repeat.repeat_live_list(2) =
  (Val.list #[.int 1, .int 2, .int 1, .int 2])

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
