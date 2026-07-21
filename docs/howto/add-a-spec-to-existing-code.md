# How to add a spec to existing Python code

Two ways: annotate the source with a `# lean[` block (the house style), or
write a sidecar Lean file and leave the source untouched. Judgment syntax:
[reference](../reference.md#the-judgment-family); design rationale:
[spec-surface.md](../spec-surface.md).

## Option A: a `# lean[` block in the source

Anatomy (from the real file `Examples/python/add.py`; the actual block
continues with the derived corollary forms before the closing `# ]` — the
anatomy is unchanged):

```python
# Examples/python/add.py (excerpt; block shortened)
def add(a, b):
    return a + b


# lean[
# /-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
# Surface.lean — fixed generous fuel; minimal-fuel pinning retired). -/
# #py_check add(2, 3) = 5
# #py_check add(-2, 3) = 1
#
# /-- The typed surface form: total correctness — `add` terminates and
# returns `a + b` — with no `Val`, no fuel, one tactic. (Not `@[spec]`: that
# attribute takes Hoare-triple/simp shapes; the ∃-fuel arrow is neither.) -/
# theorem add_total (a b : PyInt) : add(a, b) ==> a + b := by
#   py_prove [add]
# ]
```

The rules ([DESIGN.md](../DESIGN.md), "`# lean[ ... # ]` blocks", normative):

- A block opens at a line matching `# lean[` (alone on its line) and closes
  at `# ]` (alone on its line). Blocks never nest. An unclosed block is an
  extractor error.
- Inner lines lose the leading `#` and at most one following space; the rest
  is spliced **verbatim** into the companion file. Blank lines inside are fine.
- Lines starting with `import ` are hoisted (deduped) to the companion header.
- Convention: the **first** block is `#py_check` non-vacuity runs — the
  arrows are ∃-fuel statements, and the concrete runs prove the "∃" side is
  inhabited before anyone trusts a theorem.

Then, from the repo root:

```
python3 extractors/python/extract.py Examples/python/add.py
lake build
```

The extractor writes `Examples/python/add.json` (the AST envelope) and
regenerates `Examples/Add.lean` (the companion: a header with the source
sha256, `load_program add from "Examples/python/add.json"`, then your blocks
verbatim). `lake build` ingests the JSON at elaboration time and checks your
proofs. The file stem must be a valid Lean identifier — it becomes the module
constant (`add : Module`) and the surface callee (`add(a, b)`).

Which tactic closes which goal: [reference, tactic table](../reference.md#tactics).
Loop-free bodies are `py_prove [add]`; loops need `py_begin`/`py_loop`
(see `Examples/tri/proof.lean`); recursion needs `py_lift`
(see `Examples/python/fib.py`).

## Option B: a sidecar Lean file

When you cannot (or don't want to) edit the source, put theorems in a
hand-written `.lean` file. Both patterns below are the real file
`Examples/SidecarDemo.lean`, which `lake build` checks (the `Examples.+` glob
picks up any `Examples/*.lean`):

```lean
-- Examples/SidecarDemo.lean (excerpt)
/-- Sidecar pattern 1 — import the generated companion and state more
theorems about the program constant it defines (`my_abs`, loaded by
`Examples/MyAbs.lean`). Note the `Int` (not `PyInt`) binders: this proof
ends in `omega`, whose syntactic atom matching does not see through the
`PyInt` brand outside `py_begin` (which unbrands hypotheses for you). -/
theorem my_abs_nonneg (x r : Int) (h : my_abs(x) ⇓ r) : 0 ≤ r := by
  have hr : r = |x| := by py_corollary [my_abs_spec]
  omega
```

```lean
-- Examples/SidecarDemo.lean (excerpt)
load_program my_abs_again from "Examples/python/my_abs.json"

theorem my_abs_again_total (x : PyInt) : my_abs_again.my_abs(x) ==> |x| := by
  py_prove [my_abs_again]
```

Pattern 2 needs only the envelope: if the source has no `# lean[` blocks at
all, run the extractor once to produce the `.json`, load it under any fresh
name, and use the dotted callee (`my_abs_again.my_abs(x)`) — the identifier
splits into module constant and Python function name.

## What can go wrong

**Unclosed block.** Forget the closing `# ]`:

```
error: unclosed.py:4: unclosed '# lean[' block (no matching '# ]')
```

Fix: add a line containing exactly `# ]`.

**Invalid stem.** `bad-stem.py`:

```
error: bad-stem.py: stem 'bad-stem' is not a valid identifier (must match ^[A-Za-z_][A-Za-z0-9_]*$)
```

Fix: rename the file (`bad_stem.py`).

**Wrong envelope path in a sidecar.** `load_program` resolves paths against
the current working directory — the repo root under `lake build`:

```
error: load_program: cannot read 'Examples/python/nope.json': no such file or directory (error code: 4294967294)
  file: Examples/python/nope.json
(relative paths resolve against the current working directory — the package root under `lake build`; current cwd: '/home/thomas-ahle/lean_models')
```

**Doc comment on `load_program`.** `load_program` is a command, not a
declaration — a `/-- … -/` doc comment immediately before it is a parse
error (`unexpected token 'load_program'; expected …`). Use a plain `/- … -/`
comment.

**`#py_check` fails.** The check is a `#guard`, so a wrong expected value is
an elaboration error showing the exact call:

```
error: Expression
  callFunction add "add" #[ToVal.toVal 2, ToVal.toVal 3] 4096 == Res.ok (ToVal.toVal 6)
did not evaluate to `true`
```

Run the function to see what it actually returns:
`lake exe leanmodels-run Examples/python/add.json add 2 3`.

**`py_prove` on a function with a loop** fails with `unsolved goals` and a
goal containing a frozen `execWhile` applied to a large AST literal. That
leak *is* the signal: `py_prove` only does loop-free bodies — switch to
`py_begin [prog]` + `py_loop` ([Examples/tri/proof.lean](../../Examples/tri/proof.lean), and
[handle-shadowed-loop-variables.md](handle-shadowed-loop-variables.md) if the
loop mutates a variable your theorem binds).

**Companion edited by hand.** Companions are regenerated on every extractor
run (`AUTOGENERATED … DO NOT EDIT`); your edits will be overwritten. Specs
belong in the `# lean[` block or a sidecar.
