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

#py_check star_lab.list_tail(3) = (Val.list #[.int 1, .int 2, .int 3])
#py_check star_lab.list_tail(-1) = (Val.list #[.int 1, .int 2, .int (-1)])
#py_check star_lab.list_head(0) = (Val.list #[.int 0, .int 1, .int 2])
#py_check star_lab.list_two(7) = (Val.list #[.int 1, .int 2, .int 7])
#py_check star_lab.list_only() = (Val.list #[.int 1, .int 2])
#py_check star_lab.groups(5) =
  (Val.list #[.int 1, .int 2, .int 3, .int 5, .int 2, .int 3])
#py_check star_lab.empty() = (Val.list #[])

/-! ### tuple displays — the lowering with no `list(…)` wrapper at all -/

#py_check star_lab.tuple_only() = (Val.tuple #[.int 1, .int 2])
#py_check star_lab.tuple_head(9) = (Val.tuple #[.int 9, .int 1, .int 2])
#py_check star_lab.tuple_tail(9) = (Val.tuple #[.int 1, .int 2, .int 9])

/-! ### the receiver inventory is `tuple()`'s own: str, range, tuple, and
a nested display -/

#guard callFunction star_lab "from_str" #[.str "ab"] 4096
  == .ok (.list #[.str "a", .str "b"])
#guard callFunction star_lab "from_str" #[.str ""] 4096 == .ok (.list #[])
#py_check star_lab.from_range(3) = (Val.list #[.int 0, .int 1, .int 2])
#py_check star_lab.from_range(0) = (Val.list #[])
#py_check star_lab.from_tuple(3) = (Val.list #[.int 1, .int 2, .int 3])
#py_check star_lab.nested(4) = (Val.list #[.list #[.int 1, .int 2], .int 4])

/-! ### the display ALLOCATES: `[*a]` is a COPY, never an alias — which is
the whole reason `list(…)` sits on the outside -/

#py_check star_lab.fresh(9) =
  (Val.tuple #[.int 2, .int 3, .int 1, .int 9])

/-! ### the one honest MISMATCH, recorded rather than glossed: CPython says
`Value after * must be an iterable, not int`, the lowering says what
`tuple()` says. Same exception CLASS (which is what the harness compares),
different message. -/

#py_check star_lab.star_int() raises
  (.typeError "'int' object is not iterable")
#py_check star_lab.star_none() raises
  (.typeError "'NoneType' object is not iterable")

/-! ### starred `for` targets reuse the existing unpacking worker -/

#py_check star_lab.star_call() = (Val.int 3)
#py_check star_lab.star_set() = (Val.int 2)
-- the DICT receiver LANDED with §L53 rung 3b: `[*d]` is CPython's key
-- iteration, insertion-ordered. This guard asserted the refusal, and it is
-- the regression guard that flipped when the draining consumers gained
-- their dict arms (docs/memory-model.md §dict iteration).
#py_check star_lab.star_dict() = (Val.list #[.str "x", .str "y"])
#py_check star_lab.star_target() =
  (Val.tuple #[.int 1, .list #[.int 2, .int 3]])
#py_check star_lab.star_for() =
  (Val.tuple #[.int 1, .list #[.int 2], .int 3])

/-! ### what the lowering does to the heap-free fragment, pinned per
function: a LIST display leaves it (`list(…)` allocates — the exclusion
already existed for comprehensions), while a TUPLE display stays IN it,
because `tuple(…)` allocates nothing. Neither costs a proof arm. -/

#guard !((findFunction star_lab "list_tail").any FunctionDefn.heapFree)
#guard ((findFunction star_lab "tuple_head").any FunctionDefn.heapFree)
