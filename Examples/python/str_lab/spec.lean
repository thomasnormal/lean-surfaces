import LeanModels

/-!
# str_lab — the H5 string-tier acceptance set (checks-only example)

Concrete regressions for the string tier (docs/memory-model.md §string
semantics), pinned two ways: differential rows in `harness/cases.json`
(every function runs against CPython 3.9) and the `/- pass 8 (§the cast tier): int(<str>) / str(…) — the envelope was
RE-EXTRACTED for the cast-lab rows; this comment is the required real
edit (`load_program` does not track its JSON).
SUPERSEDED 2026-08-26 (qol-83): the lakefile declares
`Examples/python` as an `input_dir` in `Examples.needs`, so lake now
tracks this envelope as a build input. The real-edit ritual above is
HISTORY, not instruction. -/
#py_check str_lab.cast_int(" 42 ") = 42
#py_check str_lab.cast_int("-0") = 0
#py_check str_lab.cast_str(-3) = "-3"
#guard callFunction str_lab "cast_int" #[.str "1_2"] 4096 matches .unsupported _
#guard callFunction str_lab "cast_int" #[.str "12x3"] 4096 matches .unsupported _
#guard callFunction str_lab "cast_int" #[.str ""] 4096 matches .exn (.valueError _)
#guard callFunction str_lab "cast_str" #[.bool true] 4096 == .ok (.str "True")

#py_check`/`#guard`
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

#py_check str_lab.upper_of("abc") = "ABC"
#py_check str_lab.upper_of("nN1.") = "NN1."
#py_check str_lab.lower_flag("pq") = true
#py_check str_lab.lower_flag("pQ") = false
#guard callFunction str_lab "upper_of" #[.str "é"] 4096
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

/-! ### `%`-formatting (docs/memory-model.md §`%`-formatting on strings)

The envelope was RE-EXTRACTED for these rows. `opcode.py` line 36 is
`fmt_opcode` verbatim — a `%r` of an int inside a one-element tuple —
and it was that file's SOLE wall. Every row here is differential
(harness/cases.json); the messages are pinned by `raises` because
`diff_test` compares exception CLASSES only. -/

#py_check str_lab.fmt_opcode(0) = "<0>"
#py_check str_lab.fmt_opcode(255) = "<255>"
#py_check str_lab.fmt_opcode(-1) = "<-1>"
#py_check str_lab.fmt_repr("it's") = "\"it's\""
#py_check str_lab.fmt_repr("a\nb") = "'a\\nb'"
#py_check str_lab.fmt_repr(true) = "True"
#py_check str_lab.fmt_bare(5) = "5"
#py_check str_lab.fmt_str("x") = "x"
#py_check str_lab.fmt_str(true) = "True"
#py_check str_lab.fmt_dec(true) = "1"
#py_check str_lab.fmt_pair("depth", 7) = "depth=7"
#py_check str_lab.fmt_pct(42) = "42% done"
#py_check str_lab.fmt_noargs() = "abc"
#py_check str_lab.fmt_nonascii_s() = "héllo"

/-! The two arity `TypeError`s and the `%d` type error, verbatim (the
type name is UNQUOTED here — CPython's own wording, measured), plus the
left-to-right ORDER: the first conversion's error beats the arity of
what follows. -/

#py_check str_lab.fmt_short(1) raises
  (.typeError "not enough arguments for format string")
#py_check str_lab.fmt_leftover(1) raises
  (.typeError "not all arguments converted during string formatting")
#py_check str_lab.fmt_dec("x") raises
  (.typeError "%d format: a number is required, not str")
#py_check str_lab.fmt_dec(Val.none) raises
  (.typeError "%d format: a number is required, not NoneType")
#py_check str_lab.fmt_order("x", 1) raises
  (.typeError "%d format: a number is required, not str")

/-! The loud frontier: the minilanguage, every conversion character
outside the four, the two forms CPython itself rejects (refused rather
than given a fabricated `ValueError` — recorded restriction), a
container argument, a non-ASCII `%r`, and a mapping RHS. -/

#guard callFunction str_lab "fmt_width" #[.int 3] 4096 matches .unsupported _
#guard callFunction str_lab "fmt_hex" #[.int 255] 4096 matches .unsupported _
#guard callFunction str_lab "fmt_bad" #[.int 3] 4096 matches .unsupported _
#guard callFunction str_lab "fmt_trailing" #[.int 3] 4096 matches .unsupported _
#guard callFunction str_lab "fmt_container" #[] 4096 matches .unsupported _
#guard callFunction str_lab "fmt_nonascii_r" #[] 4096 matches .unsupported _
#guard callFunction str_lab "fmt_mapping" #[] 4096 matches .unsupported _

/-! ### The MAPPING right operand (docs/memory-model.md §`%`-formatting
on strings — "the mapping right operand", 2026-08-16)

A LIVE WRONG ANSWER, found by library mode and fixed here:
`'  x  ' % [1, 3, 5]` is `'  x  '` under CPython and was a `TypeError`
under the model. `PyUnicode_Format` sets `ctx.dict` when the right
operand passes `PyMapping_Check` and is neither a tuple nor a str, and
the trailing `not all arguments converted` check is guarded on
`!ctx.dict` — so a list or a range SUPPRESSES it. Nothing else about
the mapping path moves: `arglen = -1` already made the whole object the
single positional argument, and `%(key)s` stays loud. -/

#py_check str_lab.fmt_bare_leftover([1, 3, 5]) = "abc"
#py_check str_lab.fmt_bare_leftover(([] : List Int)) = "abc"
#py_check str_lab.fmt_range_leftover() = "abc"

/-! The other side of the same predicate: a NON-mapping leftover is
still the faithful `TypeError`, and `%d` of the whole mapping is the
faithful type error raised at the FIRST conversion. -/

#py_check str_lab.fmt_bare_leftover(1) raises
  (.typeError "not all arguments converted during string formatting")
#py_check str_lab.fmt_bare_leftover("z") raises
  (.typeError "not all arguments converted during string formatting")
#py_check str_lab.fmt_dec_seq([1, 2]) raises
  (.typeError "%d format: a number is required, not list")
#py_check str_lab.fmt_dec_seq(1) raises
  (.typeError "not enough arguments for format string")

/-! Loud, and the declared gaps: `%s` of a container is the heap walk
this operator cannot see (CPython prints `'[1]'`), and a dict RHS is
`'abc'` under CPython but never reaches the arm at all —
`evalBinOp`'s heap-operand refusal fires first. -/

#guard callFunction str_lab "fmt_seq_arg" #[.list #[.int 1]] 4096 matches .unsupported _
#guard callFunction str_lab "fmt_dict_leftover" #[] 4096 matches .unsupported _
