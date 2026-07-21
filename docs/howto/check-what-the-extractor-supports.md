# How to check what the extractor (and interpreter) supports

Coverage is layered ([DESIGN.md](../DESIGN.md), the four axes): the extractor
**never fails on constructs** — anything outside its vocabulary becomes an
`Unsupported` node in the envelope (its only errors are syntax errors,
non-identifier stems, and unclosed `# lean[` blocks) — and the interpreter
fails **loudly**
(`Res.unsupported`, with a message naming the construct) when execution
reaches anything outside the v0 semantic tier. Nothing is silently faked, so
"is my program supported?" is always answerable mechanically.

## The tier tables

The normative lists live in [DESIGN.md](../DESIGN.md):

- "Python v0 semantic tier" — supported statements/expressions/builtins.
- "Semantic decisions" — the exact rule per operator (floor division signs,
  bool/int coercion, short-circuit values, name resolution, …).

[Semantics.lean](../../LeanModels/Python/Semantics.lean)'s module docstring
additionally lists the tier-*boundary* decisions (Python-valid but v0-
unsupported: sequence repetition, `%` formatting, str unpacking, negative
`**` exponents, referencing a function as a value, …) — these yield
`unsupported`, never a fake `TypeError`.

## Read the envelope

Extract, then query the JSON (schema:
[envelope-schema.md](../envelope-schema.md)). Unsupported constructs carry
the CPython class name in `py_kind` and the unparsed source text:

```
python3 extractors/python/extract.py Examples/tri/tri.py
jq '[.. | objects | select(.kind? == "Unsupported") | .py_kind] | unique' Examples/tri/tri.json
[]
```

An empty list means everything *parses into* the supported vocabulary. On a
file using a `for` loop, the same query answers `["For"]`, and the node
itself shows what was skipped:

```json
{
  "kind": "Unsupported",
  "span": {"lineno": 2, "col_offset": 4, "end_lineno": 3, "end_col_offset": 16},
  "py_kind": "For",
  "text": "for x in xs:\n    print(x)"
}
```

`py_kind` is the CPython class name, refined for partially-supported nodes:
`"BinOp:Div"` (true division), `"Constant:float"`, `"Subscript:Slice"`,
`"AugAssign:BitOr"`, `"Compare:In"`, ….

Three per-node flags mark *callability* limits rather than parse limits —
check them per function:

```
jq '.module.body[] | select(.kind == "FunctionDef") | {name, args_unsupported, locals_unsupported}' Examples/python/add.json
{
  "name": "add",
  "args_unsupported": null,
  "locals_unsupported": null
}
```

- `args_unsupported` — non-null iff the def uses defaults/`*args`/kw-only/
  `**kwargs`/decorators; calling it is `unsupported` (positional params are
  still listed).
- `locals_unsupported` — non-null iff the body *calls* a name it also
  assigns (CPython's static-locals rule; the dynamic-env interpreter refuses
  rather than resolve it wrongly).
- `call_unsupported` on `Call` expressions — keywords / starred args at a
  call site.

## Ask the interpreter

Representable is not runnable: an `Unsupported` node only matters if
execution reaches it, and some in-vocabulary programs still leave the tier
at runtime (e.g. `2 ** -1`). The runner's `unsupported` status is the ground
truth, message included:

```
lake exe leanmodels-run Examples/python/arith.json powi 2 -1
{"status":"unsupported","msg":"'**' with a negative exponent (float result) is outside the v0 tier"}
```

In Lean, the same check is a raw `#guard` (the `unsupported` outcome is a
tier gap, not a Python result, so it deliberately has no `#py_check` form):

```lean
-- Examples/Arith.lean (generated from Examples/python/arith.py)
#guard (callFunction arith "powi" #[.int 2, .int (-1)] 20 matches .unsupported _)
```

In the differential harness, documented gaps are whitelisted per input row
with `"expect": "unsupported"`
([run-the-differential-harness.md](run-the-differential-harness.md)).

## What can go wrong

**Extraction "succeeded" but proofs are impossible.** Success is by design —
axis 2 (representation) never fails. Always run the `jq` query and a
concrete `leanmodels-run` call before writing theorems: a function whose
body is one big `Unsupported` node loads, elaborates, and satisfies no
`#py_check`.

**`unsupported` in a place CPython happily executes.** That is the loud tier
boundary, not a bug — e.g. `list += x` (in-place mutation, visible through
aliases, which value semantics cannot reproduce):

```
{"status":"unsupported","msg":"augmented assignment to a list ('+=' mutates in place, visible through aliases) is outside the v0 tier"}
```

**A whole function refuses to run** with
`function 'f' uses unsupported parameter features (defaults/varargs/kwargs/decorators)`
or `function 'f' calls a name it also assigns (CPython static-locals rule) —
outside the v0 tier`: check the two `jq` flags above; the fix is to simplify
the signature (plain positional params) or rename the local.

**Top-level code is ignored.** Statements other than `def` are recorded in
`Module.topLevel` and ignored by `callFunction` (no globals, no module-init
effects in v0). A function reading a module-level constant raises
`NameError` — faithfully to the v0 model, not to CPython. Keep everything
the function needs in its parameters.

**Vacuity.** All spec theorems are conditional on the interpreter deciding;
on an unsupported path they can hold vacuously (`~~>` is the exception — it
rules `unsupported` out, which is exactly why the weak "if it returns"
reading is not offered; see
[reference](../reference.md#the-judgment-family)). The `#py_check` first
block is the guard: concrete runs prove the function actually executes in
the tier.
