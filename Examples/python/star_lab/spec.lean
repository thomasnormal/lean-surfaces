import LeanModels

/-!
# star_lab — starred DISPLAYS, the extractor lowering (checks-only example)

`[*a, 3]` and `(1, *a)` are LOWERED by the extractor
(docs/memory-model.md §starred displays):

* `(e1, *a, e2)` ⟶ `(e1,) + tuple(a) + (e2,)`
* `[e1, *a, e2]` ⟶ `list((e1,) + tuple(a) + (e2,))`

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

Pinned loud, because these are SEPARATE constructs with separate prices
and only the display position is landed: a starred call argument
(`star_call`), a set display (`star_set`), a dict receiver (`star_dict`),
and starred assignment/`for` TARGETS (`star_target`/`star_for`).

The target refusal is a MEASURED CORRECTION, not a restatement: before
this landing the extractor kept a structural tuple target whose starred
element was `Unsupported "Starred"`, and `unpackSeq` checks ARITY BEFORE
element kinds — so `x, *y = [1, 2, 3]` answered
`ValueError: too many values to unpack (expected 2)` where CPython binds
`x = 1, y = [2, 3]`. That is a wrong answer, not a refusal. The whole
target now ingests as `Unsupported "Starred:target"` and refuses loudly.
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

/-! ### the loud frontier: the OTHER two starred positions, plus the set
display and the dict receiver -/

#guard callFunction star_lab "star_call" #[] 4096 matches .unsupported _
#guard callFunction star_lab "star_set" #[] 4096 matches .unsupported _
#guard callFunction star_lab "star_dict" #[] 4096 matches .unsupported _
#guard callFunction star_lab "star_target" #[] 4096 matches .unsupported _
#guard callFunction star_lab "star_for" #[] 4096 matches .unsupported _

/-! ### what the lowering does to the heap-free fragment, pinned per
function: a LIST display leaves it (`list(…)` allocates — the exclusion
already existed for comprehensions), while a TUPLE display stays IN it,
because `tuple(…)` allocates nothing. Neither costs a proof arm. -/

#guard !((findFunction star_lab "list_tail").any FunctionDefn.heapFree)
#guard ((findFunction star_lab "tuple_head").any FunctionDefn.heapFree)
