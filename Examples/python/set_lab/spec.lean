import LeanModels

/-!
# set_lab — H7+ sets, the honest subset (checks-only example)

Construction-from-iterable/set-comprehension + MEMBERSHIP (+ `len`, truthiness) — the
`self.history` surface, order-blind by construction. Set sorting is admitted
for deterministically ordered elements; iteration remains loud because its
hash order is never guessed,
`add`/`remove`/`pop`. Dedup rides the dict-KEY doctrine
(`set([1, True])` has one element; an unhashable element is the
faithful `TypeError`).
-/

open LeanModels LeanModels.Python

load_program set_lab from "Examples/python/set_lab/set_lab.json"

#py_check set_lab.member_int(2) = (Val.tuple #[.bool true, .bool false, .int 3])
#py_check set_lab.member_int(9) = (Val.tuple #[.bool true, .bool true, .int 4])
#py_check set_lab.member_tuple(1, 2) = (Val.tuple #[.bool true, .bool false])
#py_check set_lab.dedup_bool() = 3
#py_check set_lab.from_str("l") = (Val.tuple #[.bool true, .int 4])
#py_check set_lab.from_tuple(4) = 2
#py_check set_lab.empty_set(1) = (Val.tuple #[.bool false, .int 0, .int 0])
/-! Set displays and comprehensions remain loud source-level boundaries after
the extractor stopped lowering them (`python-completeness` §2026-11-06).
The former CPython answers remain in `-- was` comments. -/
-- was `#py_check set_lab.literal(2) = (Val.tuple #[.int 2, .bool true])`
#guard callFunction set_lab "literal" #[.int 2] 4096 matches
  .unsupported "unsupported expression 'Set:display'"
-- was `#py_check set_lab.literal(1) = (Val.tuple #[.int 1, .bool true])`
#guard callFunction set_lab "literal" #[.int 1] 4096 matches
  .unsupported "unsupported expression 'Set:display'"
-- was `#py_check set_lab.literal_unhashable() raises (.typeError "unhashable type: 'list'")`
#guard callFunction set_lab "literal_unhashable" #[] 4096 matches
  .unsupported "unsupported expression 'Set:display'"
-- was `#py_check set_lab.comprehension(7, 2) = (Val.tuple #[.int 3, .bool true])`
#guard callFunction set_lab "comprehension" #[.int 7, .int 2] 4096 matches
  .unsupported "unsupported expression 'SetComp'"
-- was `#py_check set_lab.comprehension(1, 2) = (Val.tuple #[.int 1, .bool false])`
#guard callFunction set_lab "comprehension" #[.int 1, .int 2] 4096 matches
  .unsupported "unsupported expression 'SetComp'"
#py_check set_lab.from_gen(7) = (Val.tuple #[.bool true, .int 3])
#py_check set_lab.not_in(5) = true
#py_check set_lab.unhashable_elem() raises
  (.typeError "unhashable type: 'list'")
#py_check set_lab.unhashable_probe(3) raises
  (.typeError "unhashable type: 'list'")

/-! ### set iteration uses CPython's integer hash-table order -/

#py_check set_lab.iter_is_loud(3) = 7
#guard callFunction set_lab "iter_order" #[.int (-1)] 4096 matches .unsupported _
#py_check set_lab.iter_order(7) = (Val.list #[.int 8, .int 7])
#py_check set_lab.sorted_set(2) = (Val.list #[.int 1, .int 2, .int 3])
