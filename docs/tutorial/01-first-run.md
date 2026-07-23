# Tutorial 01 — Your first run

You will push a three-line Python file through the entire pipeline: write it,
extract it, load it from a hand-written spec file, build it, run it through
the verified interpreter from the command line, and differentially test it
against CPython. No theorems yet — that is [tutorial 02](02-first-spec.md).
The point of this part is that by the end, every moving piece has moved
once, on a file *you* wrote.

## 0. Install nothing

The toolchain is pinned in `lean-toolchain`
(`leanprover/lean4:v4.33.0-rc1`); if you have elan, the first `lake build`
fetches it automatically. There are no Lean package dependencies. The
extractor and harness need only Python ≥ 3.9 standard library. Run everything
from the repository root.

The layout, in one breath: every Python example is one directory
`Examples/python/<name>/` holding the source `<name>.py`, its generated JSON envelope
`<name>.json`, and hand-written Lean files next to them — `spec.lean`
(checks and theorem statements) and, once there are real proofs,
`proof.lean`. The framework lives in `LeanModels/`, the extractor in
`extractors/python/`, the CPython differential harness in `harness/`. The
full table is in the [README](../../README.md#repo-layout).

## 1. Write the file

We use `Examples/python/tut_01/`; substitute any name you like — the stem must be
a valid identifier (`tut_01` is fine, `tut-01` is rejected, see
[What can go wrong](#what-can-go-wrong)).

```python
# Examples/python/tut_01/tut_01.py
def double(x):
    return 2 * x
```

That is the whole file. It is plain Python — nothing about it knows Lean
exists, and CPython runs it unchanged.

## 2. Extract

```console
$ python3 extractors/python/extract.py Examples/python/tut_01/tut_01.py
```

Silent on success (exit code 0). It wrote **one** file:
`Examples/python/tut_01/tut_01.json` — the AST envelope: CPython's own `ast`
module parsed your file, and the extractor dumped the tree into the
standardized JSON format ([../envelope-schema.md](../envelope-schema.md)),
next to the source. The extractor never fails on valid Python: constructs
outside the supported vocabulary become `Unsupported` nodes
([tutorial 06](06-when-proofs-fail.md) shows what happens when you *run*
one).

## 3. Write the spec file

The Lean side of the example is a hand-written file you own, not generated
output. Create `Examples/python/tut_01/spec.lean`:

```lean
-- Examples/python/tut_01/spec.lean (header comment elided)
import LeanModels

open LeanModels LeanModels.Python

load_program tut_01 from "Examples/python/tut_01/tut_01.json"

/-! Tutorial 01 (docs/tutorial/01-first-run.md): the whole pipeline on a
three-line file. Non-vacuity checks only — the theorems start in
tutorial 02. -/
#py_check tut_01.double(21) = 42
#py_check tut_01.double(0) = 0
#py_check tut_01.double(-7) = -14
```

- `load_program` reads the envelope at elaboration time and defines
  `tut_01 : Module` as a literal Lean term — your program's AST is now a
  first-class mathematical object.
- Each `#py_check` runs the function on concrete inputs through the
  interpreter **at build time** and fails the build if the result is wrong.
  `tut_01.double(…)` is the surface calling convention: module ident (the
  file stem), dot, Python function name.
- There is no `proof.lean` yet: a spec file with no theorem statements has
  no proof twin (tutorial 02 adds both).

From here on, iteration is **pure Lean**: you edit `spec.lean` (later also
`proof.lean`) and rebuild. The extractor only re-enters the loop when the
`.py` itself changes.

*Also available — inline mode.* Theorems can instead be embedded in the
`.py` inside `# lean[ … # ]` comment blocks, which the extractor splices
into a generated companion file. Exactly one example ships in that mode as
its showcase, [`Examples/python/sum_to/`](../../Examples/python/sum_to/sum_to.py); this
series teaches the three-file layout throughout.

## 4. Build

```console
$ lake build
```

`lakefile.toml` globs everything under `Examples/`, so the new spec module
is picked up automatically. During elaboration, each `#py_check` runs
`callFunction tut_01 "double" #[.int …] 4096` — the actual fuel-based
definitional interpreter ([`LeanModels/Python/Semantics.lean`](../../LeanModels/Python/Semantics.lean))
executing your actual AST — and `#guard`s the result. A green build means the
interpreter really computed `42`, `0`, and `-14`.

## 5. Run it from the command line

The same interpreter is compiled into a CLI:

```console
$ lake exe leanmodels-run Examples/python/tut_01/tut_01.json double 21
{"status":"ok","value":{"t":"int","v":"42"}}
$ lake exe leanmodels-run Examples/python/tut_01/tut_01.json double 21 --fuel 1
{"status":"timeout"}
```

One line of canonical JSON per run; the four statuses are `ok`, `exn`,
`timeout`, `unsupported` (format: [`Main.lean`](../../Main.lean),
[../DESIGN.md](../DESIGN.md)). `--fuel 1` shows the fuel discipline in the
flesh: every interpreter step consumes fuel, and running out is a `timeout`
result, not an error — this is what later makes "for *some* fuel" a
meaningful theorem statement.

## 6. Close the loop against CPython

Why believe the Lean interpreter implements Python? Because it is
differentially tested against CPython. `harness/cases.json` lists cases; the
tutorial functions are already in it:

<!-- docs-check: harness/cases.json -->
```json
  {"file": "Examples/python/tut_01/tut_01.py", "function": "double", "args": [[21], [0], [-7]], "expect": "match"},
```

(that line is verbatim from [`harness/cases.json`](../../harness/cases.json)
— append an analogous one for your own file; while experimenting you can
leave the shared list untouched and point the harness at a private one
instead, `python3 harness/diff_test.py --cases my_cases.json` — the path is
taken relative to the repo root; all flags in the
[how-to](../howto/run-the-differential-harness.md)). Then:

```console
$ python3 harness/diff_test.py
...
double(21)        ok: 42                  ok: 42                  MATCH
double(0)         ok: 0                   ok: 0                   MATCH
double(-7)        ok: -14                 ok: -14                 MATCH
...
130 cases: 0 failed, 3 whitelisted-unsupported, 127 matched
```

Left column: CPython imported your file and called the function. Middle:
`leanmodels-run` on the envelope. The harness compares canonical forms and
fails the run on any mismatch. This is the project's ground-truth discipline:
the semantics is validated against the real implementation, not against
anyone's reading of the reference manual
([../DESIGN.md](../DESIGN.md), and the how-to:
[../howto/run-the-differential-harness.md](../howto/run-the-differential-harness.md)).

## You now own the whole pipeline

```
you write .py  →  extract.py  →  .json envelope     you write spec.lean (+ proof.lean later)
                                     ↓                    ↓
              CPython  ⇄ diff_test ⇄ leanmodels-run   lake build (#py_check runs the interpreter)
```

Next: [tutorial 02](02-first-spec.md) states and proves the first theorem.

## What can go wrong

**The build fails on a `#py_check`.** Change `42` to `43` in `spec.lean`,
rebuild, and you get (reproduced on the current tree):

```
error: Expression
  callFunction tut_01 "double" #[ToVal.toVal 21] 4096 == Res.ok (ToVal.toVal 43)
did not evaluate to `true`
```

Here the value is simply wrong. The same message also appears when the cause
is fuel exhaustion or an unsupported construct — [tutorial 06,
failure mode 4](06-when-proofs-fail.md#4-a-py_check-fails--three-different-diseases-one-symptom)
shows how to tell the three apart in one `#eval`.

**Invalid stem.** Name the file `tut-01.py` and:

```
error: Examples/python/tut_01/tut-01.py: stem 'tut-01' is not a valid identifier (must match ^[A-Za-z_][A-Za-z0-9_]*$)
```

The stem becomes the Lean identifier for your module, so it must be one.

**You edited the Python but nothing changed.** There is no file watcher: the
`.json` envelope is only regenerated when you run the extractor. Until you
re-run it, `lake build` happily rebuilds the *old* program — and the
harness runs CPython on the new `.py` against Lean on the old `.json`, so
mismatches appear. Symptom: your edit seems to have no effect. Fix: re-run
`python3 extractors/python/extract.py <file>` after every source change.

**Wrong envelope path in `load_program`.** Paths resolve against the
`lake build` working directory — the repo root; a typo is a loud
elaboration error naming the path (see the
[how-to](../howto/add-a-spec-to-existing-code.md#what-can-go-wrong)).
