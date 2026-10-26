import LeanModels

/-!
# star_shadow — the starred-display lowering's shadow census (checks-only)

The lowering spells `[*a, 3]` as calls of the NAMES `list` and `tuple`,
which the source never wrote. CPython's display never looks a name up, so
a binding in the module or in the same function would make the lowered calls
resolve through the shadow — silently wrong, the one failure mode a lowering
can introduce. The extractor checks the lexical scope that contains each
display; an unrelated function's local shadow does not poison its sibling.

`shadowed` remains loud because its own local `list` shadows the synthetic
call. `elsewhere` now answers because its scope has no shadow. `plain_display`
is the control — a display with no star is not lowered, not censused, and
still answers.
-/

open LeanModels LeanModels.Python

load_program star_shadow from "Examples/python/star_shadow/star_shadow.json"

#guard callFunction star_shadow "shadowed" #[.int 3] 4096 matches .unsupported _
#py_check star_shadow.elsewhere(3) = (Val.list #[.int 1, .int 2, .int 3])

#py_check star_shadow.plain_display(3) =
  (Val.list #[.int 1, .int 2, .int 3])
