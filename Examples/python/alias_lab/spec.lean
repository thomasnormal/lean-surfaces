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
  position keeps the loud function-as-value refusal (script rows
  `alias_before_def.py` / `alias_rebound.py` pin the census's refusal
  directions).

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

/-! ### the alias is NOT a value (the refusal direction, unchanged) -/

#guard callFunction alias_lab "read_alias" #[] 4096 matches .unsupported _
