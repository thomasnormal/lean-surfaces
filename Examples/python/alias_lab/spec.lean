import LeanModels

/-!
# alias_lab — module-level def aliasing (checks-only example)

Concrete regressions for the narrow first-class slice
(docs/memory-model.md §module-level def aliasing), pinned two ways:
differential rows in `harness/cases.json` (every function AND every
alias name runs against CPython 3.9 — the alias entries are oracled by
name, not assumed) and the `#py_check`/`#guard` non-vacuity checks here.

The claims worth naming:

* **An alias call IS the direct call** — the ingestion pass makes the
  alias a second `Module.functions` entry copying the target defn, so
  `callFunction` through either name is literally the same run
  (`alias_eq_direct` below states it as term-level equality, args
  symbolic in the check's shape).
* **Alias-of-alias is transitive** (`double = scale2`), including
  through a SPLIT CHAINED assignment (`chain1 = chain2 = scale` —
  pass-5 `splitChains` runs first, so the census sees
  `chain1 = scale; chain2 = chain1`).
* **A generator def aliases too** (`pair2 = gen_pair` — the copied
  `isGenerator` flag makes the alias call allocate the H4 object), and
  **call-site keywords bind through the copied params** (`use_kw`).
* The alias never exists as a VALUE: reading `scale2` outside call
  position keeps the loud function-as-value refusal.  The script rows
  `alias_before_def.py` / `alias_rebound.py` pin the source-order behavior
  around an alias (a forward target raises `NameError`; a later ordinary
  assignment shadows an admitted alias).

No `proof.lean`: checks-only, like `drain_lab`/`kw_lab`.
-/

open LeanModels LeanModels.Python

load_program alias_lab from "Examples/python/alias_lab/alias_lab.json"

/-! ### the alias call ≡ the direct call (same run, both names) -/

#guard callFunction alias_lab "scale2" #[.int 21] 4096 ==
  callFunction alias_lab "scale" #[.int 21] 4096
#guard callFunction alias_lab "double" #[.int (-3)] 4096 ==
  callFunction alias_lab "scale" #[.int (-3)] 4096

#py_check alias_lab.scale(21) = 42
#py_check alias_lab.scale2(21) = 42
#py_check alias_lab.double(5) = 10

/-! ### transitivity, including the split chain -/

#py_check alias_lab.chain1(7) = 14
#py_check alias_lab.chain2(9) = 18

/-! ### dispatch from a function body, keywords, generators -/

#py_check alias_lab.use_alias(4) = 8
#py_check alias_lab.use_kw(5) = 15
#py_check alias_lab.use_gen_alias(3) = [3, 4]

#guard callFunction alias_lab "use_gen_alias" #[.int 10] 4096 ==
  .ok (.list #[.int 10, .int 11])
#py_check alias_lab.dead_alias() = 0
/-! The builtin-alias rows below refuse since the alias-then-call ingestion
rewrite was removed (`docs/backlog/python-completeness.md`
§2026-11-05-pycomplete-342): the alias is a first-class callable value, and
calling one is the loud boundary. The CPython answers these checks pinned
are kept in the `-- was` comments; `harness/cases.json` expects
`unsupported` for these functions. -/

-- was `#py_check alias_lab.sorted_alias(Val.tuple #[.int 3, .int 1]) = [1, 3]`
#guard callFunction alias_lab "sorted_alias" #[Val.tuple #[Val.int 3, Val.int 1]] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.max_alias(Val.tuple #[.int 3, .int 1]) = 3`
#guard callFunction alias_lab "max_alias" #[Val.tuple #[Val.int 3, Val.int 1]] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.min_alias(Val.tuple #[.int 3, .int 1]) = 1`
#guard callFunction alias_lab "min_alias" #[Val.tuple #[Val.int 3, Val.int 1]] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.abs_alias(-7) = 7`
#guard callFunction alias_lab "abs_alias" #[.int (-7)] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.int_alias("12") = 12`
#guard callFunction alias_lab "int_alias" #[.str "12"] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.float_alias("1.5") = Float64.ofBits 0x3ff8000000000000`
#guard callFunction alias_lab "float_alias" #[.str "1.5"] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.all_alias(Val.list #[.bool true, .bool false]) = false`
#guard callFunction alias_lab "all_alias" #[Val.list #[Val.bool true, Val.bool false]] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.any_alias(Val.list #[.bool false, .bool true]) = true`
#guard callFunction alias_lab "any_alias" #[Val.list #[Val.bool false, Val.bool true]] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.any_alias(Val.list #[]) = false`
#guard callFunction alias_lab "any_alias" #[Val.list #[]] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.any_alias(Val.list #[.bool false, .bool false]) = false`
#guard callFunction alias_lab "any_alias" #[Val.list #[Val.bool false, Val.bool false]] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.str_alias(17) = "17"`
#guard callFunction alias_lab "str_alias" #[.int 17] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.str_alias(true) = "True"`
#guard callFunction alias_lab "str_alias" #[.bool true] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.str_alias("quoted") = "quoted"`
#guard callFunction alias_lab "str_alias" #[.str "quoted"] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.sum_alias(Val.list #[.int 1, .int 2, .int 3]) = 6`
#guard callFunction alias_lab "sum_alias" #[Val.list #[Val.int 1, Val.int 2, Val.int 3]] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.sum_alias(Val.list #[], 5) = 5`
#guard callFunction alias_lab "sum_alias" #[Val.list #[], .int 5] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.sum_alias(Val.list #[.bool true, .bool false]) = 1`
#guard callFunction alias_lab "sum_alias" #[Val.list #[Val.bool true, Val.bool false]] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.tuple_alias(Val.list #[.int 1, .int 2]) = Val.tuple #[.int 1, .int 2]`
#guard callFunction alias_lab "tuple_alias" #[Val.list #[Val.int 1, Val.int 2]] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.tuple_alias("ab") = Val.tuple #[.str "a", .str "b"]`
#guard callFunction alias_lab "tuple_alias" #[.str "ab"] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.list_alias(Val.tuple #[.int 1, .int 2]) = Val.list #[.int 1, .int 2]`
#guard callFunction alias_lab "list_alias" #[Val.tuple #[Val.int 1, Val.int 2]] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.list_alias("ab") = ["a", "b"]`
#guard callFunction alias_lab "list_alias" #[.str "ab"] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.ord_alias("A") = 65`
#guard callFunction alias_lab "ord_alias" #[.str "A"] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.ord_alias("z") = 122`
#guard callFunction alias_lab "ord_alias" #[.str "z"] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.chr_alias(65) = "A"`
#guard callFunction alias_lab "chr_alias" #[.int 65] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.chr_alias(122) = "z"`
#guard callFunction alias_lab "chr_alias" #[.int 122] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.pow_alias(2, 10) = 1024`
#guard callFunction alias_lab "pow_alias" #[.int 2, .int 10] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.pow_alias(5, 0) = 1`
#guard callFunction alias_lab "pow_alias" #[.int 5, .int 0] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.round_alias(7) = 7`
#guard callFunction alias_lab "round_alias" #[.int 7] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.round_alias(true) = 1`
#guard callFunction alias_lab "round_alias" #[.bool true] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.ascii_alias(3) = "3"`
#guard callFunction alias_lab "ascii_alias" #[.int 3] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.ascii_alias("héllo") = "'h\\xe9llo'"`
#guard callFunction alias_lab "ascii_alias" #[.str "héllo"] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.hex_alias(15) = "0xf"`
#guard callFunction alias_lab "hex_alias" #[.int 15] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.hex_alias(-16) = "-0x10"`
#guard callFunction alias_lab "hex_alias" #[.int (-16)] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.oct_alias(9) = "0o11"`
#guard callFunction alias_lab "oct_alias" #[.int 9] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.oct_alias(-8) = "-0o10"`
#guard callFunction alias_lab "oct_alias" #[.int (-8)] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.bin_alias(5) = "0b101"`
#guard callFunction alias_lab "bin_alias" #[.int 5] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.bin_alias(-4) = "-0b100"`
#guard callFunction alias_lab "bin_alias" #[.int (-4)] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.format_alias(5) = "5"`
#guard callFunction alias_lab "format_alias" #[.int 5] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.format_alias(true) = "True"`
#guard callFunction alias_lab "format_alias" #[.bool true] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#guard callFunction alias_lab "range_alias" #[.int 3] 4096 == .ok (.range (.int 0) (.int 3) (.int 1))`
#guard callFunction alias_lab "range_alias" #[.int 3] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.next_alias(3) = 0`
#guard callFunction alias_lab "next_alias" #[.int 3] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.next_alias(0) = -1`
#guard callFunction alias_lab "next_alias" #[.int 0] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"
-- was `#py_check alias_lab.print_alias(5) = (Val.none)`
#guard callFunction alias_lab "print_alias" #[.int 5] 4096 matches
  .unsupported "calling a first-class callable value is outside the tier"

/-! ### the alias is NOT a value (the refusal direction, unchanged) -/

#guard callFunction alias_lab "read_alias" #[] 4096 == .ok (.callable "scale2")
