import LeanModels

/-!
# star_shadow — the starred-display lowering's shadowing check (checks-only)

The lowering spells `[*a, 3]` as calls of unspellable synthetic builtin
names. CPython's display never looks a source name up, so bindings of `list`
or `tuple` cannot change the generated calls.

Both `shadowed` and `elsewhere` answer because the synthetic calls use
unspellable builtin names. `plain_display` is the control — a display with no
star is not lowered and still answers.
-/

open LeanModels LeanModels.Python

load_program star_shadow from "Examples/python/star_shadow/star_shadow.json"

/-! Since the extractor stopped lowering starred displays
(`docs/backlog/python-completeness.md` §2026-11-06-pycomplete-361),
`shadowed` and `elsewhere` refuse; `plain_display` is unchanged. The CPython
answers these checks pinned are kept in the `-- was` comments;
`harness/cases.json` expects `unsupported` for these functions. -/

-- was `#py_check star_shadow.shadowed(3) = (Val.list #[.int 1, .int 2, .int 3])`
#guard callFunction star_shadow "shadowed" #[.int 3] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_shadow.elsewhere(3) = (Val.list #[.int 1, .int 2, .int 3])`
#guard callFunction star_shadow "elsewhere" #[.int 3] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"

#py_check star_shadow.plain_display(3) =
  (Val.list #[.int 1, .int 2, .int 3])
