import LeanModels

/-!
# str_lab — the H5 string-tier acceptance set (checks-only example)

Concrete regressions for the string tier (docs/memory-model.md §string
semantics), pinned two ways: differential rows in `harness/cases.json`
(every function runs against CPython 3.9) and the `#py_check`/`#guard`
non-vacuity checks here (kernel-evaluated).

The headline behaviors: slices are CPython-exact for every string —
both step directions, omitted bounds (ingestion's `Constant None`
normalization), negative indices, out-of-range clamping, and the
STEP-FIRST validation order (`order_probe`: a zero step's `ValueError`
beats the lower bound's `TypeError`, exactly `PySlice_Unpack`);
`swapcase`/`isupper` are the ASCII case maps (non-ASCII refuses
loudly — Unicode tables are not guessed); `index` is code-point-exact
substring search with the faithful `ValueError` miss. The loud
frontier: any other str method (`upper` — never a fake
`AttributeError`), list/tuple slices (they ALLOCATE in CPython), and
`index` start/end arguments. No `proof.lean`: checks-only, like
`cls_lab`/`list_lab` — the string-tier theorems on the shipped file
live in `Examples/python/sunfish`.
-/

open LeanModels LeanModels.Python

load_program str_lab from "Examples/python/str_lab/str_lab.json"

/-! ### slices: both directions, defaults, clamping, negatives -/

#py_check str_lab.rev("abcdef") = "fedcba"
#py_check str_lab.rev("") = ""
#py_check str_lab.mid("hello", 1, 3) = "el"
#py_check str_lab.mid("abcdef", -4, -1) = "cde"
#py_check str_lab.mid("abcdef", 4, 1) = ""
#py_check str_lab.mid("abcdef", -100, 100) = "abcdef"
#py_check str_lab.head("abcdef", 2) = "ab"
#py_check str_lab.tail("abcdef", 2) = "cdef"
#py_check str_lab.every_second("abcdef") = "ace"
#py_check str_lab.back_step("abcdef", 5, 1) = "fd"
#py_check str_lab.copy_all("abc") = "abc"

/-! ### the method trio -/

#py_check str_lab.swap("aBcD") = "AbCd"
#py_check str_lab.swap("PNBRQK.pnbrqk ") = "pnbrqk.PNBRQK "
#py_check str_lab.isup("ABC1") = true
#py_check str_lab.isup("AbC") = false
#py_check str_lab.isup("123") = false
#py_check str_lab.isup("") = false
#py_check str_lab.idx("abcab", "b") = 1
#py_check str_lab.idx("abcab", "ab") = 0
#py_check str_lab.idx("abc", "") = 0

/-! ### sunfish's two string shapes: rotate's flip chain and move's put -/

#py_check str_lab.board_flip("KQkq") = "QKqk"
#py_check str_lab.put("abcde", 2, "X") = "abXde"

/-! ### faithful errors, CPython's validation order included -/

#py_check str_lab.slice_of_int(5) raises
  (.typeError "'int' object is not subscriptable")
#py_check str_lab.step_zero("abc") raises
  (.valueError "slice step cannot be zero")
#py_check str_lab.bad_lower("abc", "x") raises
  (.typeError "slice indices must be integers or None or have an __index__ method")
#py_check str_lab.order_probe("abc", "x") raises
  (.valueError "slice step cannot be zero")
#py_check str_lab.swap_arg_raises("abc") raises
  (.typeError "swapcase() takes no arguments (1 given)")
#py_check str_lab.idx_arg_raises("abc", 1) raises
  (.typeError "must be str, not int")
#py_check str_lab.idx("abc", "zz") raises
  (.valueError "substring not found")

/-! ### the loud frontier, pinned raw (no surface form for
`unsupported` — deliberate): out-of-tier str methods are never a fake
`AttributeError`; allocating slices and `index` bounds refuse. -/

#guard callFunction str_lab "upper_is_loud" #[.str "abc"] 4096
  matches .unsupported _
#guard callFunction str_lab "list_slice_is_loud" #[] 4096
  matches .unsupported _
#guard callFunction str_lab "idx_start_is_loud" #[.str "abcab", .str "b", .int 2] 4096
  matches .unsupported _
#guard callFunction str_lab "swap" #[.str "é"] 4096 matches .unsupported _
#guard callFunction str_lab "isup" #[.str "É"] 4096 matches .unsupported _

/-! ### the slice NODE stays in the heap-free fragment (H5: str slices
are pure values; allocating receivers refuse loudly) — pinned per
function, since the module is not heap-free (`list_slice_is_loud`'s
display allocates). Str METHOD calls conservatively leave the fragment
for now, exactly like every `sorted` call (the attribute whitelist is
still `.get`-only — recorded gap, docs/backlog.md), so `swap`/
`board_flip` are deliberately not pinned here. -/

#guard (findFunction str_lab "rev").any FunctionDefn.heapFree
#guard (findFunction str_lab "put").any FunctionDefn.heapFree
