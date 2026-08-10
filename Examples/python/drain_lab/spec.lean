import LeanModels

/-!
# drain_lab — the H6 draining consumers (checks-only example)

Concrete regressions for the draining tier (docs/memory-model.md
§draining consumers), pinned two ways: differential rows in
`harness/cases.json` (every function runs against CPython 3.9) and the
`#py_check`/`#guard` non-vacuity checks here (kernel-evaluated).

The claims worth naming:

* **`sorted`/`max`/`min` DRAIN a generator** through the H4 stepper —
  effects interleave, the object ends closed, and the values then take
  the same path as a value-list argument.
* **`any`/`all` STOP at the first deciding element** — `all_stops`/
  `any_stops` iterate the REMAINDER after the call, so a design that
  drains eagerly answers the wrong count; `any_infinite` consumes
  `count()` and terminates, so a design that drains fully diverges.
* **One ordering relation** — general-order `sorted` and the `<`
  operator share `rvalLt`: tuples lexicographic and class-erased, strs
  by code point, bools kept AS BOOLS (`sorted([1, True, 0, False, 2])`
  is CPython's `[0, False, 1, True, 2]`), and `reverse=True` is
  descending STABLE insertion (`[2, 1, True, 0, False]` — a reversal
  would forge `[..., False, 0]`).
* **Mixed value kinds refuse loudly** — CPython raises `TypeError` on
  `sorted([1, "s"])`; the tier never guesses the class.

No `proof.lean`: checks-only, like `gen_lab`/`kw_lab`.
-/

open LeanModels LeanModels.Python

load_program drain_lab from "Examples/python/drain_lab/drain_lab.json"

/-! ### full drains -/

#guard callFunction drain_lab "sorted_gen" #[.int 6, .int 7] 10000 ==
  .ok (.list #[.int 0, .int 1, .int 2, .int 2, .int 4, .int 4])
#guard callFunction drain_lab "sorted_gen_rev" #[.int 6, .int 7] 10000 ==
  .ok (.list #[.int 4, .int 4, .int 2, .int 2, .int 1, .int 0])
#py_check drain_lab.max_gen(6, 7) = 4
#py_check drain_lab.min_gen(6, 7) = 0
#py_check drain_lab.max_gen_empty() raises
  (.valueError "max() arg is an empty sequence")

/-! ### the general order: one relation with `<` -/

#guard callFunction drain_lab "sorted_tuples" #[.int 1, .int 2] 10000 ==
  .ok (.list #[.tuple #[.int 1, .str "a"], .tuple #[.int 1, .str "x"],
               .tuple #[.int 2, .str "a"]])
#guard callFunction drain_lab "sorted_tuples_rev" #[.int 1, .int 2] 10000 ==
  .ok (.list #[.tuple #[.int 2, .str "a"], .tuple #[.int 1, .str "x"],
               .tuple #[.int 1, .str "a"]])
#guard callFunction drain_lab "sorted_str" #[.str "cab"] 10000 ==
  .ok (.list #[.str "a", .str "b", .str "c"])
#guard callFunction drain_lab "sorted_bools" #[] 10000 ==
  .ok (.list #[.int 0, .bool false, .int 1, .bool true, .int 2])
-- descending STABLE — the reversal forgery is the negative control
#guard callFunction drain_lab "sorted_bools_rev" #[] 10000 ==
  .ok (.list #[.int 2, .int 1, .bool true, .int 0, .bool false])
#py_check drain_lab.max_str("pear") = "r"
#py_check drain_lab.max_tuples(1, 2) = (Val.tuple #[.int 2, .str "a"])

/-! ### short-circuit: the partial drain is OBSERVABLE -/

#py_check drain_lab.all_stops(2) = (Val.tuple #[.bool false, .int 2])
#py_check drain_lab.all_stops(9) = (Val.tuple #[.bool true, .int 0])
#py_check drain_lab.any_stops(3) = (Val.tuple #[.bool true, .int 1])
#py_check drain_lab.any_stops(9) = (Val.tuple #[.bool false, .int 0])
#py_check drain_lab.any_infinite() = true
#py_check drain_lab.all_of_str("") = true
#py_check drain_lab.any_of_list(0, 0) = false
#py_check drain_lab.all_of_tuple(1, 2) = true

/-! ### the loud frontier -/

#guard (match callFunction drain_lab "sorted_mixed" #[.int 1] 10000 with
  | .unsupported _ => true | _ => false)
