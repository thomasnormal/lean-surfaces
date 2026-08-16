import LeanModels

/-!
# star_shadow — the starred-display lowering's shadow census (checks-only)

The lowering spells `[*a, 3]` as calls of the NAMES `list` and `tuple`,
which the source never wrote. CPython's display never looks a name up, so
a module BINDING either name would make the lowered calls resolve through
the shadow — silently wrong, the one failure mode a lowering can
introduce. The extractor censuses the whole module (any scope, any
binding form) and refuses every starred display in it.

Whole-module and conservative BY DESIGN: `elsewhere` has no shadow of its
own and is refused anyway, because deciding it per scope would mean
re-deciding CPython's scoping rules inside the extractor. `plain_display`
is the control — a display with no star is not lowered, not censused, and
still answers.
-/

open LeanModels LeanModels.Python

load_program star_shadow from "Examples/python/star_shadow/star_shadow.json"

#guard callFunction star_shadow "shadowed" #[.int 3] 4096 matches .unsupported _
#guard callFunction star_shadow "elsewhere" #[.int 3] 4096 matches .unsupported _

#py_check star_shadow.plain_display(3) =
  (Val.list #[.int 1, .int 2, .int 3])
