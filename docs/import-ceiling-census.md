# The import-ceiling census

Of the stdlib files the completeness sweep REFUSES on `import`, how many
could be admitted in principle once import support lands (their transitive
import closure is pure Python inside the pinned CPython 3.9 stdlib), and
how many are hard-blocked because the closure reaches a C module?

Instrument: `harness/import_census.py` (which reuses
`harness/import_closure.py`'s module table and walks). Seed set: the
`REFUSE` rows of a fresh `harness/leanpy_survey.py --stdlib` sweep whose
static wall set contains `import` — partitioned into **import-only**
(`import` is the sole wall) and **import+other** (the file also contains
another wall, so admitting imports alone cannot admit it). The partition
is kept clean: the headline counts are reported per bucket, never merged.

## Pre-registered classification rules

Committed BEFORE the census was run. The results section below was empty
in the commit that registered these rules.

**What counts as a C module.** The pinned interpreter's own inventory,
asked by subprocess and never imported: `sys.builtin_module_names` of
CPython 3.9 (Homebrew 3.9.19), plus every `.so`/`.pyd`/`.dylib` stem in
its `lib-dynload`. Name convention (a leading underscore) is evidence of
nothing.

**How imports are resolved.** Statically, by `ast.parse` of
`Import`/`ImportFrom` nodes; no module's code is ever executed. Dotted
imports demand every prefix (`a.b.c` demands `a`, `a.b`, `a.b.c`).
Relative imports resolve against the importing module's package (its own
name for a package `__init__`, the parent otherwise). `from p import x`
demands `p`, and demands `p.x` only if `p.x` resolves to a module —
otherwise `x` is an attribute of `p`, not a missing module. Star imports
demand the named module (its re-exports are followed through the module,
not the star). The closure is breadth-first, so reported depths are true
distances.

**Scope.** IMPORT-TIME: imports in the module body, including under a
module-level `if`/`try`/`for` — these execute when the module loads — and
excluding `def`/`class`/`lambda` bodies, which do not. The seed's own
`if __name__ == "__main__":` guard is live (leanpy runs seeds as
programs); the guard of every module it imports is dead. Imports under
`if TYPE_CHECKING:` (or `typing.TYPE_CHECKING`) are excluded as
runtime-false and recorded in a side note.

**The accelerator tie-break.** A module-level `try` whose handlers catch
`ImportError` (or `ModuleNotFoundError`, or anything that swallows them:
bare `except:`, `Exception`, `BaseException`) splits its imports into an
accelerator branch (the `try` body and `else`) and a fallback branch (the
handler bodies). Every seed gets TWO closures: **FULL** (accelerators
succeed: body followed, fallback not) and **STRICT** (accelerators fail:
body dropped, fallback followed). A name imported on both sides, or
unguarded anywhere, is `always`.

**Verdicts**, in decision order:

| verdict | rule |
| --- | --- |
| `NO-IMPORT` | both closures are just the seed — its `import` wall is inside a function body, not at import time |
| `C-BLOCKED` | the STRICT closure reaches a C module: even with every accelerator absent, C runs |
| `UNRESOLVED` | the STRICT closure demands, unguarded, a module the pinned platform does not ship — reported apart, never folded into pure |
| `PURE-ACCEL` | STRICT closure pure; FULL reaches C only through optional accelerator branches — a Python-only module system runs the fallback and admits the file |
| `PURE` | both closures pure Python within the pinned stdlib |

A module missing only behind an `except ImportError` guard (a platform
branch) is recorded per-seed as `optional-missing` — counted and listed,
never silently dropped, never a blocker.

**Controls, gated.** `import_census.py` refuses to run the census unless
both control suites pass first: a synthetic fixture in which every rule
above has a row built to falsify it (including a PURE row — a classifier
that answers C-BLOCKED for everything must fail loudly), and four
real-table controls: `import keyword` must be PURE (`keyword.py` in
3.9.19 was verified by hand to contain zero import statements),
`import math` and `import _socket` must be C-BLOCKED, and
`import zzz_no_such_module` must be UNRESOLVED.

## Results

(To be filled by the census run; empty at pre-registration.)

## What this census cannot see

(To be filled with the run; the static-blindness statement is part of the
deliverable, not a disclaimer added if convenient.)
