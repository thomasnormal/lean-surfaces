# The completeness census, and the ladder off it

**The question.** Not "does the model run sunfish" — that is the proof
campaign's question and it drives. This one: *how much of ARBITRARY
Python does the model run, which constructs stop it, and what does each
one cost to admit?*

**The law.** Census before pricing, pricing before grind — and every
census claim is a RUN. This file states no coverage number that was read
off the source; each one is produced by `harness/refusal_census.py`,
which extracts a witness, runs it under the pinned CPython 3.9 oracle,
runs it through the model, and compares. Recorded verdicts that
disagreed with the measurement were CORRECTED BY THE MEASUREMENT — five
of them on the first run, listed in §5, and four of those five are the
ladder's cheapest rung.

    python3 harness/refusal_census.py            # all three censuses
    python3 harness/refusal_census.py --grammar --keep /tmp/w

The instrument exits nonzero on DRIFT: a witness whose verdict moved, a
whitelisted row with no construct class, a loud row the model stopped
refusing. It is a regression check on the census, not a report.

## 1. Why a `MATCH` is a lower bound and a refusal message is an upper one

A grammar witness that matches claims exactly this: *the production is
reachable, and the model agreed with CPython on this program.* It does
not claim the production is wholly in tier — `op.Mult` matches on
`2 * 3` and refuses on `"ab" * 3`; `op.Pow` matches on `2 ** 3` and
refuses on `2 ** -1`. Both boundaries are themselves witnesses here
(`op.Mult-repetition`, `op.Pow-negative`), which is the discipline: when
a match is known to have an edge, the edge gets its own row rather than
a footnote.

The complementary bound is the refusal-message inventory (§4), which is
read off the source and is an upper bound: it names every construct the
model can refuse, including ones no witness reaches. Neither table
substitutes for the other. §L14 recorded why in the sharpest possible
form — a statement-level `Unsupported` count is not an ingestion verdict,
because `yield from` a non-genexp is a STRUCTURED node that refuses at
EVALUATION. Run the thing.

## 2. The grammar census — 86 witnesses, 60 MATCH, 26 REFUSE

One witness per production of CPython 3.9's `ast` grammar: 25
statements, 27 expressions, 13 binary / 4 unary / 10 comparison / 2
boolean operators, plus the four `Constant` payload types the extractor
forks on and two measured edge rows.

**The 26 refusals, by sort.**

| sort | refused | witnesses |
| --- | --- | --- |
| `stmt` (25) | 11 | `AsyncFunctionDef` `AsyncFor` `AsyncWith` `AnnAssign` `With` `Raise` `Try` `Import` `ImportFrom` `Global` `Nonlocal` |
| `expr` (27) | 4 | `Set` `SetComp` `DictComp` `Await` |
| `Constant` payload (4) | 4 | `float` `bytes` `complex` `ellipsis` |
| `operator` (13) | 4 | `Div` `RShift` `BitXor` `MatMult` |
| `unaryop` (4) | 2 | `UAdd` `Invert` |
| edge rows (2) | 1 | `Pow-negative` |
| `cmpop` (10), `boolop` (2) | 0 | — |

**Then rungs 1, 2 and 3b landed**, so the table above is the census AS
TAKEN and the current numbers are **105 witnesses, 74 MATCH, 31
REFUSE**: `RShift`, `BitXor`, `UAdd` and `Invert` moved to MATCH and
`RShift-budget` joined as an edge row (rung 1); `AnnAssign-local` joined
as a MATCH and `AnnAssign-novalue` as a refusal, with `stmt.AnnAssign`
itself staying REFUSE because its witness is module-scope (rung 2); and
sixteen `dict.*` rows joined as rung 3's acceptance battery, three of
which measured MATCH and re-scoped the rung, six more flipping when 3b
landed. The taken-table is kept rather than overwritten — it is what the
ladder was priced against.

**25 of the 26 are gaps; one is faithful.** `1 @ 2` is a `TypeError` in
CPython too, so `op.MatMult` costs a program nothing — no operand type in
or out of tier has `__matmul__`. Every other refusal stops a program
CPython runs.

**Four sorts are COMPLETE**: every comparison operator, both boolean
operators, and — with the two edges named — the whole of assignment,
control flow (`If`/`While`/`For`/`Break`/`Continue`/`Pass`), function and
class definition, generators (`Yield`/`YieldFrom`), comprehension of
lists, f-strings in their bare form, and both display forms.

**One sort is entirely absent**: `async` (`AsyncFunctionDef`, `AsyncFor`,
`AsyncWith`, `Await` — four productions, one refusal message, because the
`async def` refuses first and the three inner productions are never
reached).

## 3. The two refusal corpora, classified by MEASURED message

`harness/cases.json`'s `"expect": "unsupported"` rows are the recorded
gaps of the CLOSED-FUNCTION surface; `harness/scripts.json`'s are the
WHOLE-PROGRAM surface's. Both are bucketed by the refusal message the
model actually produced, against a construct class recorded per row in
the instrument. A whitelisted row with no class fails the run — the
census covers the whole whitelist, or it is not one.

**113 whitelisted rows, 44 classes** as taken (118 in 46 classes after
rungs 1-2: `>>`'s budget row joined `<<`'s in `op.LShift-budget`, and
`annassign.no-value` / `annassign.non-simple-target` are new). The head:

| class | rows | representative |
| --- | --- | --- |
| `exc.handler` | 10 | `exc_lab::as_binding` |
| `del.name-set-census` | 6 | `del_lab::read_after` |
| `exc.raise` | 6 | `rsa_inverse::inverse` |
| `set.order` | 6 | `set_lab::iter_is_loud` |
| `closure.admission` | 5 | `closure_lab::def_in_loop` |
| `format.percent-heap-operand` | 5 | `str_lab::fmt_container` |
| `firstclass.callable` | 4 | `cls_lab::class_as_value` |
| `format.percent-minilanguage` | 4 | `str_lab::fmt_width` |
| `genexp.lowering-admission` | 4 | `gen_lab::walrus_leak` |
| `range.observation` | 4 | `seq_lab::range_eq` |
| `shadow.module-census` | 4 | `star_shadow::shadowed` |

then 3 rows each for `builtin.int-of-str`, `fstring.conversion`,
`starred.position`, `str.non-ascii`; 2 each for `assign.non-name-target`,
`attr.on-scalar`, `boundary.generator`, `boundary.heap-value`,
`boundary.list-mutation`, `boundary.namedtuple`, `clock.underrun`,
`del.non-name-target`, `fstring.format-spec`, `iter.dict`,
`kwargs.callee-kind`, `namedtuple.protocol`, `op.Is-immediates`,
`slice.allocating`; and 1 each for 17 more.

**Two readings the classification forces.**

* **Exceptions are the largest single class and the tier has MOVED under
  the record.** `exc.handler` + `exc.raise` + `exc.finally` is 17 of 113
  rows. But the measured message says `'except AssertionError:': only an
  admitted exception class (class N(Exception): pass) or the pinned
  import …` — a user-defined exception class IS admitted today. What is
  left is BUILTIN handler classes, `as` bindings, `else`, bare `except`,
  tuple handlers, `raise <expression>`, `raise C(args)`, bare re-raise,
  `raise … from …` and `finally`. AGENTS.md still describes exceptions as
  deferred wholesale; that is stale.
* **Nine classes are BOUNDARY, not language.** `boundary.*` (7 rows) and
  `firstclass.callable` (4) refuse because `Val` — the observation type
  the differential harness compares — has no form for a dict, a list
  mutation, a namedtuple, a range, a generator, a closure or an instance.
  A program never meets them: leanpy runs whole files and compares
  stdout. These 11 rows price the HARNESS, not the language, and belong
  in a different queue from the rest.

**14 loud scripts, 9 classes** as taken (15 in 10 after rung 2 added
`annassign.module-scope`): `del.definition-name` 3;
`alias.admission`, `class.creation-effect`, `script.definition-order` 2
each; `format.percent-minilanguage`, `import.position`, `set.order`,
`starred.position`, `str.non-ascii` 1 each.

## 4. The refusal points in the source — the upper bound

Counted, not sampled.

| layer | points | shape |
| --- | --- | --- |
| interpreter + ingestion | **143** distinct `.unsupported "…"` literals in `LeanModels/Python/*.lean` | of which **16** are `internal: … (report this)` — heap/dispatch invariants that should be unreachable, so **127** are reachable refusals |
| extractor, literal | **11** `py_kind`s | `NamedExpr` `Starred:target` `Starred:display_shadowed` `Dict:unpack` five `JoinedStr:*` two `ImportFrom:accelerator-*` |
| extractor, computed | **6** families | `BinOp:` `UnaryOp:` `Compare:` `AugAssign:` `Constant:` `Subscript:` — one refusal per unmodelled member of each operator table |
| extractor, generic | **3** fall-throughs | every `ast` node type with no clause: expression, statement, and the top-level dispatcher |
| extractor, structured-but-loud | **6** envelope fields | `args_` `call_` `class_` `closure_` `locals_` `try_unsupported` — the node IS extracted, carries a prose reason, and refuses at EVALUATION. This is the family a node count cannot see (§L14). |

The 127 reachable interpreter refusals concentrate hard. The largest
groups, by the property they protect:

* **hash order** — 12 messages (`for`/`sorted`/`list`/`tuple`/`sum`/`set`/
  `enumerate`/unpacking over a set, `set.pop`, `print` of a set, an
  assert message that is a set). Genuinely unknowable; these are
  permanent by doctrine, not a rung.
* **live dict iteration** — 10 messages, and NOT the same kind of
  refusal. See rung 3.
* **stateful generator drain** — 8 messages (`in`/`sorted`/`max`/`min`/
  `sum`/`tuple`/`enumerate`/unpacking a generator CONSUMES it).
* **boundary observation forms** — 9 messages, one per `Val`-less kind.
* **keyword arity of builtins and methods** — 7 messages.
* **`range` observation** — 6 messages.
* **module-top-level flow** — 4 messages (`return`/`break`/`continue`/loop
  flow at top level). All FAITHFUL: CPython raises `SyntaxError` at
  compile time, so these cost nothing.

## 5. What the measurement CORRECTED

Five of the 86 grammar rows were recorded from a reading of the source
and measured otherwise. Four became the cheapest rung on the ladder.

| row | recorded | MEASURED | what it means |
| --- | --- | --- | --- |
| `op.RShift` | MATCH | **REFUSE** | `>>` is not in `BinOp`; `<<` landed and its mirror did not |
| `op.BitXor` | MATCH | **REFUSE** | `^` is not in `BinOp`; `\|` and `&` landed |
| `op.UAdd` | MATCH | **REFUSE** | `UnaryOp` is `usub \| not`; unary `+` is not in it |
| `op.Invert` | MATCH | **REFUSE** | nor is `~` |
| `op.Pow` | REFUSE | **MATCH** | `**` IS in tier; only the float-valued negative exponent refuses |

The reading that produced the four wrong MATCHes was "the bitwise tier
landed" — true of `<<`, `|`, `&` and false of their three siblings. No
amount of re-reading `docs/backlog.md` would have found it; one
`print(5 ^ 3)` did.

## 6. THE LADDER

Ordered by (price, unblocked value), §L14's pricing style. "Price" is
implementation cost including the proof layer; "unblocks" names concrete
Python, not a category.

### Rung 1 — the four missing integer operators. Price: TRIVIAL. **LANDED.**

`>>`, `^`, unary `+`, unary `~`. Two `BinOp` constructors, two `UnaryOp`
constructors, four extractor table entries, four evaluation arms, one
`intXor`. Built in the same pass that censused it —
docs/memory-model.md §the operator remainder. `BinOp` is now missing only
`Div` and `MatMult`, both out by KIND; `UnaryOp` is complete.

**The proof layer cost TWO `rfl` arms, not the zero this rung predicted**
— and the miss is the rung's most transferable finding.
`fuelMono`/`worldInv`/`clockErase` are operator-generic as the
`BinOp:BitAnd` precedent says, so the two `BinOp` constructors really were
free and the build carried 3545 of 3685 jobs. It stopped at
`evalUnaryOpH_swapAt`, which `cases op` exhaustively because
`evalUnaryOpH` exists at all (`not` reads the heap for dict truthiness,
while `evalBinOp` is pure and no blindness lemma mentions it). The site
was invisible to the survey that priced the rung for one character:
`match` arms are written `| .usub =>` and `cases op with` arms are
written `| usub =>`, and the grep had the dot. **Grep an operator sort's
constructors without the leading dot.** Nothing allocates, so
`Expr.heapFree` is untouched, and `>>=`/`^=` came free with the
`ALLOWED_BINOPS` entries.

**Unblocks**: hashing and checksum code (`h ^= b`, `h >> 5`), mask idioms
(`x & ~mask`), bitboards, `struct`-shaped packing, and every `+n` written
for symmetry with `-n`.

**Why the census found this and re-reading did not.** The record on each
of the four is different, and none of them says "hard":

* `>>` was deferred *with a reason* — §bitwise `&` says it "needs a
  budget decision it shares with a pre-existing hole in `<<`". The same
  batch closed that hole with `shiftBudget`. **The deferral outlived its
  cause by four passes.**
* `^` is named in that same section as "a rider that can be added the
  same way if `^` is ever wanted". Nobody wanted it, so nobody added it.
* `~` was measured as the **sole** static next wall of a stdlib module in
  the library sweep's next-wall table — a real blocker, counted and left.
* `+x` is mentioned nowhere in the repository.

So the earlier phrasing of this finding, "nothing recorded about the
omission", is CORRECT only of `+x`. The other three were recorded, in
three different places, none of which is where a person looks to ask
"which operators run?". That is the argument for a census being an
instrument rather than a reading: `print(5 ^ 3)` needs no index.

**Risk**: none realized. `intXor`'s arms and `Int.fdiv`-as-`>>` were
checked against CPython 3.9.19 over 95481 + 24720 pairs, 0 mismatches,
before a line of Lean was written. `>>` takes `<<`'s budget refusal
rather than CPython's saturation — loud, never a claim CPython raises,
with saturation recorded as owed.

### Rung 2 — `AnnAssign`. Price: SMALL. **LANDED (function bodies).**

`x: int = 1` was the single most common construct in modern Python that
this model refused outright, and it refused the WHOLE FILE.

The semantics split by scope, and the split is what made it cheap — one
extractor clause, no interpreter change, no proof-layer change, no new
AST node. docs/memory-model.md §annotated assignment is the contract.

**Measured, not read off PEP 526**: in a function body the annotation is
never evaluated, so `x: boom() = 1` and `x: Undef = 1` both run clean
inside a `def` and both raise at module scope. That is what makes the
rewrite exact with NO condition on the annotation expression.

**Three shapes stay loud, each for a measured reason.** Module and class
scope evaluate the annotation and write `__annotations__` (after storing
the value — the order is measured). A value-less `x: int` binds nothing
but LOCALISES its name, so dropping it would read a module global where
CPython raises `UnboundLocalError` — the one shape whose quiet narrowing
would be a silent wrong answer, pinned by
`ann_lab.ann_novalue_shadows_global`. Non-simple targets still evaluate
their annotation.

**Unblocks**: typed application and library code, where a single
annotated local used to cost the whole module.

**Owed**: module scope is admissible as a two-statement ingestion rewrite
(assign, then the annotation as an expression statement, in CPython's
measured order), because `__annotations__` is unobservable in tier. Not
taken here because one-statement-into-two moves `Module.topLevel`
indices that the proof campaign's pins are stated against.

### Rung 3 — live dict iteration. **CENSUSED; re-scoped into four inches.**

Ten interpreter refusal messages ride on this, and the census corrected
the rung twice before a line of it was written.
docs/memory-model.md §dict iteration carries the measurements.

**CORRECTION 1 — the cursor is already BUILT.** `for k, v in d.items():`
at MODULE scope runs today, in insertion order, allowing value updates
and raising CPython's `RuntimeError: dictionary changed size during
iteration` VERBATIM on a mid-loop insert. The same loop inside a `def`
refuses. So rung 3 is an EXTENSION of a working cursor to the
closed-function surface, not a construction, and its `RuntimeError` is
inherited rather than invented.

**CORRECTION 2 — a same-size key-set change is not modellable, ever.**
Deleting a key BEHIND the cursor and inserting one raises a SECOND,
different `RuntimeError: dictionary keys changed during iteration`;
moving the same deletion AHEAD of the cursor answers `[1, 2, 99]` with no
error; bulk churn that restores the size answers with the NEW keys. The
three differ only by entries-array layout and compaction, so that regime
is permanently LOUD. **The cross-rung dependency**: it is unreachable
today only because `del d[k]` refuses first, and it becomes REQUIRED the
day dict deletion lands.

**The inches, ordered by price:**

* **3b — the draining consumers — LANDED.** `list`/`tuple`/`sorted`/
  `sum`/`max`/`min`/`set`/`any`/`all`/`[*d]`. **No mutation window
  exists** — they drain with no user code in between — so none of the
  hazards can arise, and they need only "the keys, in insertion order":
  one `dictKeys` helper and seven value arms, each the `.list` arm beside
  it. *The recorded refusals cited "live dict iteration" for all of them:
  they guarded a hazard only two of them can meet.* The proof-layer price
  was 19 walker arms across `PayloadBlind` and `ClockErase`, predicted by
  §L53 before the inch was written and every one the adjacent `.list`
  tactic verbatim.
* **3a — the cursor at function scope and the bare `for k in d` form**:
  a mutual-block member plus its four walker arms.
* **3c — the view methods as iterables** and `enumerate(d)`.
* **3d — `DictComp`**, which rides 3a.

**Unblocks**: dict iteration, one of the two or three most common idioms
in Python.

### Rung 4 — exceptions, the remainder. Price: MEDIUM-LARGE.

17 of 113 whitelisted rows, one grammar production (`Try`), four
interpreter messages — and, per §3, a tier that has ALREADY moved: a
user-defined `class N(Exception): pass` handler is admitted today.

What is left needs one thing the model does not have: an exception
VALUE. `PyErr` is a closed enum, so `except ValueError`, `raise
C(args)`, `as e`, bare re-raise and `raise … from …` all need a class +
args object and a subclass relation for handler matching. `else` and
`finally` are flow, and cheaper. Sequence the value first; the flow
arms fall out.

**Unblocks**: `try/except` at large — a substantial fraction of stdlib
and application code — and rung 6 (`with`) behind it.

### Rung 5 — allocating slices and sequence repetition. Price: SMALL.

`xs[a:b]` on a LIST, and `"ab" * 3` / `[0] * n`. Three interpreter
messages plus `op.Mult-repetition`. The tuple halves of both are ALREADY
in tier — `seqSlice` slices a tuple/namedtuple and `tupleRepeat` repeats
one under a budget, and the shipped sunfish's padding line
(`(0,) * 20 + pst[k] + (0,) * 20` over `table[i*8 : i*8+8]`) runs
through exactly those. What is missing is the half whose result is a
fresh HEAP object.

That is also why the price is small: the shape is already paid for.
`list(iterable)` allocates and left `Expr.heapFree`, with `worldInv`
gaining one `hlstx` conjunct, `fuelMono` one `bind` arm and `clockErase`
one `allocList` leaf. A list slice is that pattern again over a computed
index range, and the bound validation is `strSlice`'s, verbatim.

**Unblocks**: `xs[1:]`, `xs[:-1]`, `[0] * n` — the ordinary spelling of
half of all list manipulation.

### Named, and deliberately NOT in the top five

* **`float`** — the largest gap by value and by price simultaneously.
  Four grammar rows depend on it (`const.float`, `op.Div`,
  `op.Pow-negative`, and `str()`/`repr()` of one). It is not a work item
  but a DECISION: Lean's `Float` is not kernel-reducible, so `#py_check`
  and every captured `rfl` run would break on it — the same family as
  the mergeSort trap. It needs an owner-gated design (an exact-rational
  or IEEE-simulation core), not a session.
* **The boundary observation forms** — 11 whitelisted rows, but they
  price the differential HARNESS, not the language. A separate queue.
* **`with` / context managers** — rides rung 4 and the dunder guard.
* **`SetComp` / `DictComp`** — ride rung 3 and the `dict(<pairs>)`
  hashability question.
* **`nonlocal` and cell WRITES** — already priced in §L14 ("the write
  plus a `Res.mapOk` blindness lemma beside `heapAttrStore_swapAt`");
  nothing shipped needs it.
* **`import`** — measured worthless for the stdlib in §the import
  ceiling (0 of 154 refusers have a pure-Python closure). It stays low
  for stdlib and is the only door for third-party pure-Python packages.
* **`async`** — four productions, near-zero verification value.

## 7. The recorded over-refusals

A refusal where CPython succeeds AND the model could be right is a bug
class of its own, and the census tracks them rather than letting them
read as tier boundaries.

| row | CPython | why it refuses |
| --- | --- | --- |
| `gen_lab::yf_leak_drive` | answers | the genexp arm keeps an inadmissible INLINING un-lowered rather than falling through to the fresh-target path |
| `del_lab::rebind_after` | returns 99 | the del name-set census does not clear on rebind |
| `del_lab::loop_del` | returns 6 | the same census, in a loop |
| `star_shadow::elsewhere` | builds `[1, 2, 3]` | the shadow census is whole-MODULE; this function has no shadow |
| `fstring_shadow::elsewhere` | renders `'3'` | the same census, for `str` |

The two `elsewhere` rows are a deliberate trade recorded at the time
(deciding it per scope means re-deciding CPython's scoping rules inside
the extractor, a second table). The `del` pair and the `yield from` row
are not trades; they are the cheapest correctness inches on this list
and each is one census clause.

`nonlocal`, by contrast, is refused BY DESIGN and the design holds for
arbitrary Python: the closure tier reads cells at the CALL from the
defining frame, so a write-back has no place to land. It is a rung
(above), not an over-refusal.
