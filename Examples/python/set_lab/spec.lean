import LeanModels

/-!
# set_lab — H7+ sets, the honest subset (checks-only example)

Construction-from-iterable + MEMBERSHIP (+ `len`, truthiness) — the
`self.history` surface, order-blind by construction. Everything else is
loud: iteration and `sorted(set)` (hash order, never guessed),
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
#py_check set_lab.from_gen(7) = (Val.tuple #[.bool true, .int 3])
#py_check set_lab.not_in(5) = true
#py_check set_lab.unhashable_elem() raises
  (.typeError "unhashable type: 'list'")
#py_check set_lab.unhashable_probe(3) raises
  (.typeError "unhashable type: 'list'")

/-! ### the loud frontier: hash order is never guessed -/

#guard (match callFunction set_lab "iter_is_loud" #[.int 3] 10000 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction set_lab "sorted_is_loud" #[.int 2] 10000 with
  | .unsupported _ => true | _ => false)
