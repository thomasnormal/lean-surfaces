import LeanModels

/-!
# star_lab — starred DISPLAYS, the extractor lowering (checks-only example)

`[*a, 3]`, `{*a, 3}`, `(1, *a)` and `pair(*a)` are LOWERED by the extractor
(docs/memory-model.md §starred displays):

* `(e1, *a, e2)` ⟶ `(e1,) + tuple(a) + (e2,)`
* `[e1, *a, e2]` ⟶ `list((e1,) + tuple(a) + (e2,))`
* `{e1, *a}` ⟶ `set(list((e1,) + tuple(a)))`
* `f(e1, *a, e2)` ⟶ `f(e1, <star-arg>(a), e2)` with in-place expansion

Zero new AST constructors, zero `evalExpr` arms, zero walkers, ZERO proof
arms — `fuelMono`/`worldInv`/`ceExecStmt_succ` do not move. The obvious
lowering `list(a) + [3]` is the WRONG one: `list(…)` allocates a heap
object and `evalBinOp`'s `.ref` arm refuses concatenation of heap objects
loudly, so `list(…)` appears only on the OUTSIDE — where a fresh list is
exactly what CPython builds — and `tuple(…)`, the immediate-value
constructor, is the only thing `+` ever sees.

Evaluation order survives the lowering, which is what a lowering most
easily breaks: `+` associates left and the `binOp` arm binds left before
right, so the operands run in source order (`star_script.py` pins it
through stdout).

Pinned boundaries remain separate constructs: starred call arguments expand
admitted eager iterables in place, while flat assignment and `for` targets use
the dedicated `UnpackAssign` worker. Nested and otherwise unsupported target
shapes remain loud.
-/

open LeanModels LeanModels.Python

load_program star_lab from "Examples/python/star_lab/star_lab.json"

/-! ### list displays: a star at the tail, the head, twice, and alone -/

/-! Since the extractor stopped lowering starred displays, starred call
arguments and starred `for` targets (`docs/backlog/python-completeness.md`
§2026-11-06-pycomplete-361), the lowering described above is retired and
every starred row below refuses (`star_target`, the flat unpacking
assignment, still answers). The CPython answers these checks pinned are kept
in the `-- was` comments; `harness/cases.json` expects `unsupported` for
these functions. -/

-- was `#py_check star_lab.list_tail(3) = (Val.list #[.int 1, .int 2, .int 3])`
#guard callFunction star_lab "list_tail" #[.int 3] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.list_tail(-1) = (Val.list #[.int 1, .int 2, .int (-1)])`
#guard callFunction star_lab "list_tail" #[.int (-1)] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.list_head(0) = (Val.list #[.int 0, .int 1, .int 2])`
#guard callFunction star_lab "list_head" #[.int 0] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.list_two(7) = (Val.list #[.int 1, .int 2, .int 7])`
#guard callFunction star_lab "list_two" #[.int 7] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.list_only() = (Val.list #[.int 1, .int 2])`
#guard callFunction star_lab "list_only" #[] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.groups(5) = (Val.list #[.int 1, .int 2, .int 3, .int 5, .int 2, .int 3])`
#guard callFunction star_lab "groups" #[.int 5] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.empty() = (Val.list #[])`
#guard callFunction star_lab "empty" #[] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"

/-! ### tuple displays — the lowering with no `list(…)` wrapper at all -/

-- was `#py_check star_lab.tuple_only() = (Val.tuple #[.int 1, .int 2])`
#guard callFunction star_lab "tuple_only" #[] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.tuple_head(9) = (Val.tuple #[.int 9, .int 1, .int 2])`
#guard callFunction star_lab "tuple_head" #[.int 9] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.tuple_tail(9) = (Val.tuple #[.int 1, .int 2, .int 9])`
#guard callFunction star_lab "tuple_tail" #[.int 9] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"

/-! ### the receiver inventory is `tuple()`'s own: str, range, tuple, and
a nested display -/

-- was `#guard callFunction star_lab "from_str" #[.str "ab"] 4096 == .ok (.list #[.str "a", .str "b"])`
#guard callFunction star_lab "from_str" #[.str "ab"] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#guard callFunction star_lab "from_str" #[.str ""] 4096 == .ok (.list #[])`
#guard callFunction star_lab "from_str" #[.str ""] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.from_range(3) = (Val.list #[.int 0, .int 1, .int 2])`
#guard callFunction star_lab "from_range" #[.int 3] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.from_range(0) = (Val.list #[])`
#guard callFunction star_lab "from_range" #[.int 0] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.from_tuple(3) = (Val.list #[.int 1, .int 2, .int 3])`
#guard callFunction star_lab "from_tuple" #[.int 3] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.nested(4) = (Val.list #[.list #[.int 1, .int 2], .int 4])`
#guard callFunction star_lab "nested" #[.int 4] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"

/-! ### the display ALLOCATES: `[*a]` is a COPY, never an alias — which is
the whole reason `list(…)` sits on the outside -/

-- was `#py_check star_lab.fresh(9) = (Val.tuple #[.int 2, .int 3, .int 1, .int 9])`
#guard callFunction star_lab "fresh" #[.int 9] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"

/-! ### the one honest MISMATCH, recorded rather than glossed: CPython says
`Value after * must be an iterable, not int`, the lowering says what
`tuple()` says. Same exception CLASS (which is what the harness compares),
different message. -/

-- was `#py_check star_lab.star_int() raises (.typeError "'int' object is not iterable")`
#guard callFunction star_lab "star_int" #[] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
-- was `#py_check star_lab.star_none() raises (.typeError "'NoneType' object is not iterable")`
#guard callFunction star_lab "star_none" #[] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"

/-! ### starred `for` targets reuse the existing unpacking worker -/

-- was `#py_check star_lab.star_call() = (Val.int 3)`
#guard callFunction star_lab "star_call" #[] 4096 matches
  .unsupported "unsupported expression 'Starred:call'"
-- was `#py_check star_lab.star_set() = (Val.int 2)`
#guard callFunction star_lab "star_set" #[] 4096 matches
  .unsupported "unsupported expression 'Set:display'"
-- the DICT receiver LANDED with §L53 rung 3b: `[*d]` is CPython's key
-- iteration, insertion-ordered. This guard asserted the refusal, and it is
-- the regression guard that flipped when the draining consumers gained
-- their dict arms (docs/memory-model.md §dict iteration).
-- was `#py_check star_lab.star_dict() = (Val.list #[.str "x", .str "y"])`
#guard callFunction star_lab "star_dict" #[] 4096 matches
  .unsupported "unsupported expression 'Starred:display'"
#py_check star_lab.star_target() =
  (Val.tuple #[.int 1, .list #[.int 2, .int 3]])
-- was `#py_check star_lab.star_for() = (Val.tuple #[.int 1, .list #[.int 2], .int 3])`
#guard callFunction star_lab "star_for" #[] 4096 matches
  .unsupported "unsupported statement 'Starred:target'"

/-! ### what the lowering does to the heap-free fragment, pinned per
function: a LIST display leaves it (`list(…)` allocates — the exclusion
already existed for comprehensions), while a TUPLE display stays IN it,
because `tuple(…)` allocates nothing. Neither costs a proof arm. -/

#guard !((findFunction star_lab "list_tail").any FunctionDefn.heapFree)
#guard ((findFunction star_lab "tuple_head").any FunctionDefn.heapFree)
