import LeanModels

/-!
# seq_lab — pass 3's value tiers at function level (checks-only example)

Tuple/namedtuple slices (a namedtuple slice is a PLAIN tuple), tuple
repetition, `sum(it[, start])` (the element fold IS `evalBinOp .add`; a
str start is CPython's special-cased `TypeError`), `tuple(it)`, and
`range` as the immediate `RVal.rangeV` — materialize-per-use, which is
what makes RE-ITERATION exact (`range_reiter`). The loud frontier is
pinned below: range `==`/indexing/membership/unpacking/boundary, list
slices, str repetition — every one `unsupported`, never a guessed value
and never a fake `TypeError`.
-/

open LeanModels LeanModels.Python

load_program seq_lab from "Examples/python/seq_lab/seq_lab.json"

/-! ### slices -/

#py_check seq_lab.slice_tuple(2, 6) =
  (Val.tuple #[.int 30, .int 40, .int 50, .int 60])
#py_check seq_lab.slice_computed(1) = (Val.tuple #[.int 30, .int 40])
#py_check seq_lab.slice_step(-2) =
  (Val.tuple #[.tuple #[.int 6, .int 4, .int 2],
               .tuple #[.int 5, .int 4, .int 3],
               .tuple #[.int 4, .int 5, .int 6]])
#py_check seq_lab.slice_move(3) = (Val.tuple #[.int 3, .int 10])

/-! ### repetition -/

#py_check seq_lab.repeat(3) =
  (Val.tuple #[.int 0, .int 0, .int 0, .int 7, .int 7])
#py_check seq_lab.repeat(-1) = (Val.tuple #[.int 7, .int 7])
#py_check seq_lab.repeat_left(2) =
  (Val.tuple #[.int 1, .int 2, .int 1, .int 2])
#py_check seq_lab.repeat_bool() = (Val.tuple #[.int 1, .int 2])

/-! ### sum -/

#py_check seq_lab.sum_ints(4) = 10
#py_check seq_lab.sum_start(10) = 13
#py_check seq_lab.sum_tuples() = (Val.tuple #[.int 1, .int 2, .int 3])
#py_check seq_lab.sum_gen(5) = 30
#py_check seq_lab.sum_str_start() raises
  (.typeError "sum() can't sum strings [use ''.join(seq) instead]")
#py_check seq_lab.sum_str_elems() raises
  (.typeError "unsupported operand type(s) for +: 'int' and 'str'")
#py_check seq_lab.sum_arity() raises
  (.typeError "sum() takes at most 2 arguments (3 given)")

/-! ### tuple() -/

#py_check seq_lab.tuple_of_str("ab") = (Val.tuple #[.str "a", .str "b"])
#py_check seq_lab.tuple_of_list(3) =
  (Val.tuple #[.int 1, .int 2, .int 3, .int 4])
#py_check seq_lab.tuple_of_gen(3) = (Val.tuple #[.int 0, .int 2, .int 4])
#py_check seq_lab.tuple_of_range(3) = (Val.tuple #[.int 3, .int 2, .int 1])
#py_check seq_lab.tuple_of_int() raises
  (.typeError "'int' object is not iterable")

/-! ### range -/

#py_check seq_lab.range_len(1, 10, 3) = 3
#py_check seq_lab.range_len(5, 1, -2) = 2
#py_check seq_lab.range_for(4) = 14
#py_check seq_lab.range_reiter(4) = (Val.tuple #[.int 6, .int 6])
#py_check seq_lab.range_truthy(0) = 0
#py_check seq_lab.range_truthy(2) = 1
#py_check seq_lab.range_zero_step() raises
  (.valueError "range() arg 3 must not be zero")
#py_check seq_lab.range_next() raises
  (.typeError "'range' object is not an iterator")
#py_check seq_lab.range_extremum(5) = (Val.tuple #[.int 4, .int 0])
#py_check seq_lab.range_empty_max() raises
  (.valueError "max() arg is an empty sequence")
#py_check seq_lab.enum_range(4) = 32

/-! ### the loud frontier (unsupported, never guessed) -/

#guard (match callFunction seq_lab "range_eq" #[.int 3] 4096 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction seq_lab "range_index" #[.int 3] 4096 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction seq_lab "range_in" #[.int 5] 4096 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction seq_lab "range_boundary" #[.int 3] 4096 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction seq_lab "range_unpack" #[] 4096 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction seq_lab "list_slice_loud" #[.int 2] 4096 with
  | .unsupported _ => true | _ => false)
#guard (match callFunction seq_lab "str_repeat_loud" #[.int 2] 4096 with
  | .unsupported _ => true | _ => false)

/-! ### pass 5: left shift and bitwise or (docs/memory-model.md §left
shift and bitwise or) — the post-#158 shipped file's `1 << 63` and
`live |= …`. `<<` is exact multiplication on all ints (negative count
the faithful ValueError); `|` decides boolness first (`True | False`
IS a bool — the differential rows pin the type through the harness's
typed JSON), nonneg ints are the binary or, a negative operand is
loudly out. -/

#py_check seq_lab.shl(1, 63) = 9223372036854775808
#py_check seq_lab.shl(-3, 4) = -48
#py_check seq_lab.shl_deadline() = 9223372036854775808
#py_check seq_lab.shl(5, -1) raises (.valueError "negative shift count")
#py_check seq_lab.bor(6, 3) = 7
#py_check seq_lab.bor(0, 0) = 0
#py_check seq_lab.bor_aug(5) = true
#py_check seq_lab.bor_aug(2) = false

#guard callFunction seq_lab "bor" #[.bool true, .bool false] 4096 == .ok (.bool true)
#guard callFunction seq_lab "bor" #[.bool true, .int 2] 4096 == .ok (.int 3)
#guard callFunction seq_lab "shl" #[.str "a", .int 1] 4096 ==
  .exn (.typeError "unsupported operand type(s) for <<: 'str' and 'int'")
#guard callFunction seq_lab "bor_neg" #[.int (-1)] 4096 matches .unsupported _
