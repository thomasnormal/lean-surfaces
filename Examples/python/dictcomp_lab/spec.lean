import LeanModels.Python

open LeanModels LeanModels.Python

load_program dictcomp_lab from "Examples/python/dictcomp_lab/dictcomp_lab.json"

/-! The dict comprehensions below refuse since the extractor stopped lowering
comprehensions (`docs/backlog/python-completeness.md`
§2026-11-06-pycomplete-361); `bad_pair` and `bad_length` (no comprehension)
still answer. The CPython answers these checks pinned are kept in the
`-- was` comments; `harness/cases.json` expects `unsupported` for these
functions. -/

-- was `#py_check dictcomp_lab.from_range(5, 3) = (Val.tuple #[.int 5, .int 9])`
#guard callFunction dictcomp_lab "from_range" #[.int 5, .int 3] 4096 matches
  .unsupported "unsupported expression 'DictComp'"
-- was `#py_check dictcomp_lab.from_range(2, 7) = (Val.tuple #[.int 2, .int (-1)])`
#guard callFunction dictcomp_lab "from_range" #[.int 2, .int 7] 4096 matches
  .unsupported "unsupported expression 'DictComp'"
-- was `#py_check dictcomp_lab.duplicate_keys(5) = (Val.tuple #[.int 4, .int 3])`
#guard callFunction dictcomp_lab "duplicate_keys" #[.int 5] 4096 matches
  .unsupported "unsupported expression 'DictComp'"
#py_check dictcomp_lab.bad_pair() raises
  (.typeError "cannot convert dictionary update sequence element #0 to a sequence")
#py_check dictcomp_lab.bad_length() raises
  (.valueError "dictionary update sequence element #0 has length 1; 2 is required")
-- was `#py_check dictcomp_lab.unhashable_key() raises (.typeError "unhashable type: 'list'")`
#guard callFunction dictcomp_lab "unhashable_key" #[] 4096 matches
  .unsupported "unsupported expression 'DictComp'"
