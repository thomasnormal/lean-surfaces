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

## Results (2026-08-14; machine-readable rows in `import-ceiling-census.json`)

Sweep: 167 stdlib seeds, 162 REFUSE, of which **154 refuse with `import`
in the wall set** — 8 import-only, 146 import+other. Both control suites
green before the census ran. All four decisive verdicts below were
re-checked by hand against the 3.9.19 source.

| bucket | files | PURE | PURE-ACCEL | C-BLOCKED | UNRESOLVED |
| --- | ---: | ---: | ---: | ---: | ---: |
| import-only | 8 | 0 | 1 | 7 | 0 |
| import+other | 146 | 0 | 3 | 143 | 0 |
| **total** | **154** | **0** | **4** | **150** | **0** |

**THE CEILING IS 4/154.** No stdlib file refusing on `import` has a pure
closure outright; four (`bisect`, `opcode`, `quopri`, `stat`) are pure
behind an optional C accelerator — `try: from _bisect import * except
ImportError:` with a pure fallback — and the other 150 execute C on every
branch. The number the backlog wanted before committing to a module
system: closing `import` for pure-Python closures buys ONE sweep file
(`bisect`, the only PURE-ACCEL in the import-only bucket) plus three more
behind their other walls (`opcode` needs `del`, `stat` needs `&`,
`quopri` needs bytes literals — all tail constructs already designed).

**The shortlist is flat.** All four admissible closures have size 2 (the
seed plus its guarded accelerator); none imports another pure module, so
every closure in-degree is 0 and there is no unlock cascade to rank. The
import FORMS they need are correspondingly narrow: absolute
`from X import names` and `from X import *` inside `try`/`except
ImportError` — a missing module must raise a catchable `ImportError` —
and NOTHING else: no plain `import X` binding, no relative imports, no
dotted packages. That is the whole implementation surface the admissible
set pays for.

**Per-seed caveat, recorded not buried:** `quopri` is admissible as an
importable module, but the sweep runs seeds as programs, and its
`__main__` guard calls `main()`, whose body does `import sys, getopt` at
runtime — so the sweep's `quopri` row still refuses (or reaches C) after
import support lands. The program-mode flip set is `bisect` alone among
import-only files.

**Why the wall is this high:** the strict-closure C blockers are the
interpreter and the OS, not computation — `sys` (140 of 150 C-blocked
seeds), `_weakref` (127), `builtins` (106), `itertools` (104), `_thread`
(100), `posix` (88), `_sre` (84), `_io` (76). Nine seeds are one C module
from pure (`enum`, `codeop`, `formatter`, `_sitebuiltins` need only
`sys`; `sre_compile`/`sre_constants` only `_sre`; `operator` only
`builtins`; `contextvars` only `_contextvars`; `struct` only `_struct`) —
the modellable-by-kind split and the greedy native-core cover for that
follow-up decision live in `harness/import_closure.py`.

Instrument notes. (1) The runner binary predates this session's
uncommitted `.lean` edits (fstring lane); refusal-on-import is not among
the changed behaviors, and the model batch ran 167 files in 1.3 s.
(2) This sweep says import present-in-154 / sole-in-8 where the
backlog's 2026-08-13 row said 155/7: the working tree's extractor edits
are part of the envelope cache key, so the wall census moved one file
between buckets (`import` remains the frontier either way).

## What this census cannot see

The closure is static, so it is blind to dynamic imports —
`__import__(name)`, `importlib.import_module(...)` — which resolve a
module from a runtime string no `ast` walk can evaluate; 14 modules in
the walked closures contain one (`encodings`, `pickle`, `pkgutil`,
`warnings`, `doctest`, `inspect`, `runpy`, `sysconfig`, …), so a verdict
whose closure passes through them could under-count C reachability. It
also does not follow function-body imports (pre-registered import-time
scope; the `quopri` caveat above shows the pattern), takes both sides of
version/platform `if`s at module level, and treats a
`from p import x` that does not resolve as an attribute access rather
than a missing module. None of these blind spots can flip a C-BLOCKED
verdict to pure: 145 of the 150 reach C through imports that are direct
children of the module body (statically certain to execute; measured
with `import_closure.py`'s UNCONDITIONAL scope), and the remaining five
(`abc`, `decimal`, `hashlib`, `heapq`, `numbers`) are blocked on the
branch a Python-only system actually runs — the pure fallback itself
reaches C (`abc` falls back to `_py_abc`, which needs `_weakref`;
`decimal` to `_pydecimal`, which needs `_contextvars`) or the seed's own
live `__main__` guard does (`heapq` imports `doctest`). The blind spots
could only make a PURE(-ACCEL) verdict generous, which is why the four
winners were audited by hand.
