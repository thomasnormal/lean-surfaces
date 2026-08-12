import LeanModels

/-!
# iter_lab — the H5 iteration-tier acceptance set (checks-only example)

Concrete regressions for container membership, `for` over a str, and the
`ord`/`chr` pair (docs/memory-model.md §string semantics), pinned two
ways: differential rows in `harness/cases.json` (every function runs
against CPython 3.9) and the `#py_check`/`#guard` non-vacuity checks
here (kernel-evaluated).

The headline behaviors: `in` is now decided for EVERY in-tier container
— a str is CPython's SUBSTRING test (never element membership, and the
faithful `'in <string>' requires string as left operand` `TypeError`
otherwise), while value tuples, boundary lists and namedtuples scan
their elements with the same `element == probe` convention as heap
lists; `for` over a str walks its CODE POINTS (a snapshot IS the live
semantics there — strs are immutable, so unlike `execForList`'s heap
cursor nothing can be observed mid-loop); `ord`/`chr` are code-point
exact, with `chr` out of `range(0x110000)` the faithful `ValueError`
and a SURROGATE code point refused loudly (Lean's `Char` cannot
represent one — a silent substitution would be wrong). No `proof.lean`:
checks-only, like `str_lab`/`cls_lab`/`list_lab`.
-/

open LeanModels LeanModels.Python

load_program iter_lab from "Examples/python/iter_lab/iter_lab.json"

/-! ### membership on strs: SUBSTRINGS, not elements -/

#py_check iter_lab.in_str("abcdef", "cd") = true
#py_check iter_lab.in_str("abcdef", "ce") = false
#py_check iter_lab.in_str("abcdef", "") = true
#py_check iter_lab.in_str("", "") = true
#py_check iter_lab.in_str("", "a") = false
#py_check iter_lab.not_in_str("abcdef", "cd") = false
#py_check iter_lab.not_in_str("abcdef", "ce") = true

/-! ### gen_moves' two hot tests (sunfish.py, `Position.gen_moves`) -/

#py_check iter_lab.piece_test("P") = true
#py_check iter_lab.piece_test("\n") = true
#py_check iter_lab.piece_test(" ") = true
#py_check iter_lab.piece_test(".") = false
#py_check iter_lab.piece_test("p") = false
#py_check iter_lab.promo_test("p") = true
#py_check iter_lab.promo_test("K") = false

/-! ### membership on value containers -/

#py_check iter_lab.in_tuple(20) = true
#py_check iter_lab.in_tuple(21) = false
#py_check iter_lab.not_in_tuple(21) = true
#py_check iter_lab.in_ntuple(3) = true
#py_check iter_lab.in_ntuple(4) = true
#py_check iter_lab.in_ntuple(5) = false

/-! ### `for` over a str -/

#py_check iter_lab.count_char("banana", "a") = 3
#py_check iter_lab.count_char("", "a") = 0
#py_check iter_lab.take_until("abcdef", "d") = "abc"
#py_check iter_lab.take_until("abcdef", "z") = "abcdef"
#py_check iter_lab.sum_ords("AB") = 131
#py_check iter_lab.sum_ords("") = 0

/-! ### ord / chr -/

#py_check iter_lab.ord_of("A") = 65
#py_check iter_lab.ord_of(" ") = 32
#py_check iter_lab.chr_of(65) = "A"
#py_check iter_lab.chr_of(10) = "\n"
#py_check iter_lab.roundtrip(97) = 97
#py_check iter_lab.shift("abc", 1) = "bcd"

/-! ### the faithful exceptions -/

#py_check iter_lab.ord_of("ab") raises
  (.typeError "ord() expected a character, but string of length 2 found")
#py_check iter_lab.ord_of(5) raises
  (.typeError "ord() expected string of length 1, but int found")
#py_check iter_lab.in_int(3) raises
  (.typeError "argument of type 'int' is not iterable")
#py_check iter_lab.in_str_bad_left("abc", 1) raises
  (.typeError "'in <string>' requires string as left operand, not int")
#py_check iter_lab.chr_out_of_range(1114112) raises
  (.valueError "chr() arg not in range(0x110000)")
#py_check iter_lab.chr_out_of_range(-1) raises
  (.valueError "chr() arg not in range(0x110000)")

/-! ### the loud frontier (raw `#guard`: `unsupported` has no surface form) -/

#guard callFunction iter_lab "chr_surrogate" #[] 4096 matches .unsupported _

/-! ### membership on a BOUNDARY list argument (`RVal.listV`) -/

#guard callFunction iter_lab "in_list" #[.list #[.int 1, .int 2], .int 2] 4096
  == .ok (.bool true)
#guard callFunction iter_lab "in_list" #[.list #[.int 1, .int 2], .int 3] 4096
  == .ok (.bool false)

/-! ### `enumerate` in a module with NO generator def (2026-08-13)

`enumerate(…)` allocates a generator FRAME (`enumSeq`), which
`moduleGenFree` used to claim impossible without a generator `def` — so
the `for`-over-generator arm refused ordinary Python with
`internal: … heap well-formedness violation — report this`. Found by
`tools/leanpy`; the predicate now also walks for `enumerate`/`count`
calls (`Expr.genAllocFree`), and iter_lab is the module that pins it,
having no generator definition of its own. -/

#guard !moduleGenFree iter_lab
#py_check iter_lab.enum_sum("PNBRQK") = 1155
#py_check iter_lab.enum_sum("") = 0
#py_check iter_lab.enum_sum("a") = 0
#py_check iter_lab.enum_first("PNB") = 80
#py_check iter_lab.enum_first("") = -1

/-! ### the membership/`for`/`ord`/`chr` nodes stay in the heap-free
fragment (they neither allocate nor mutate) — pinned per function, since
the module itself is not heap-free (`Pt` is a class-free namedtuple, but
`count_char`'s `for` over a str and the rest are what matters here). -/

#guard (findFunction iter_lab "piece_test").any FunctionDefn.heapFree
#guard (findFunction iter_lab "count_char").any FunctionDefn.heapFree
#guard (findFunction iter_lab "shift").any FunctionDefn.heapFree
