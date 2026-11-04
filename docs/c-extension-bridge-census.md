# C as a third language — the extension-bridge census (OWNER-GATED)

**Status: price-tag memo, nothing here is built, and no recommendation is
made.** The question on the table: add C as a third modeled language
(after Python and SystemVerilog) specifically to EXECUTE CPython stdlib
extension modules — `_struct.c` running for real under the definitional
interpreter, instead of the intrinsics proposal's name-only bindings
(`docs/c-intrinsics-proposal.md`). This memo measures what that costs and
what it flips, from the sources, so the owner's decision is decidable.
Whether to build any of it is the owner's call; a modeled C API is a
claim about interpreter internals this project would then be
answerable for.

Sources pinned: `Python-3.9.19.tar.xz` from python.org, sha256
`d4892cd1618f6458cb851208c030df1482779609d0f3939991bd38184f8c679e` —
the same 3.9.19 the census and the sweep pin. Machine-readable rows in
`docs/c-extension-bridge-census.json`; instrument described in §1.
Nothing below is quoted from memory.

## 1 What was measured

For each candidate module's C source (comments and string literals
stripped, so a `PyErr_SetString` in a docstring does not count):

- **API surface**: every `Py*`/`_Py*`/`METH_*`/`T_*` identifier the file
  references — calls, macros, and types alike — deduplicated and
  filtered against the set of identifiers actually declared in the
  pinned tree's `Include/**/*.h` (3,139 names), so module-internal
  helpers that happen to wear the prefix are excluded.
- **Buckets**, split into two classes. *Boilerplate* (mechanical under a
  bridge — handled once by a fixed pattern or a no-op): argument
  parsing/`Py_BuildValue`; refcount macros; type-object/module-init
  machinery (`PyTypeObject` slots, `PyModuleDef`, `METH_*`,
  `PyDoc_STRVAR`); allocation/GC (`PyMem_*`, `Py_VISIT` — under the
  model's heap these are the heap tier, not semantics); GIL/thread
  macros; core substrate names (`PyObject`, `Py_ssize_t`);
  `_Py_IDENTIFIER` interning; C `ctype` macros. *Semantic* (each name is
  a behavior the bridge must get right, faithfully to CPython): object
  protocol (`PyObject_RichCompareBool`, `PySequence_GetItem`);
  number/long/float conversion; str/bytes construction; containers;
  buffer protocol; exception raising (faithful errors are load-bearing
  in this repo); everything unclassified. The split is judgment and the
  JSON keeps every name, so re-splitting is a script run, not a redo.
- **libc calls** (`memcpy`, `strtod`, `floor`, …): the price of the C
  *language* tier itself, distinct from the CPython API bridge.
- **float usage**: `double`/`float` keyword occurrences plus `PyFloat_*`
  API use — the float gate the intrinsics memo already enforces.
- **file-scope `static` non-`const` data**: mutable module state, the
  thing that breaks "a module is a pure value". Hand-audited below,
  because method tables are `static` but morally `const`.
- **`goto`/`switch` density**: a proxy for how much of C's control
  surface the C tier must model beyond structured code.

Candidates were chosen by kind (algorithmic, per the coordinator's
classification) crossed with the import-ceiling census's blocking data,
plus three controls chosen to fail for three different reasons: `math`
(float-gated), `zlib` (semantics live in an external library), `_socket`
(effect-class).

## 2 The per-module table

LoC is non-blank lines of the listed files. "API" is distinct CPython
API names referenced; "sem" the semantic subset; "int" the
underscore-internal (`_Py*`) subset — names with NO stability contract.

| module | files | LoC | API | sem | int | libc | floats | state (audited) | verdict |
| --- | --- | ---: | ---: | ---: | ---: | ---: | --- | --- | --- |
| `_bisect` | `_bisectmodule.c` | 212 | 20 | 10 | 2 | 0 | none | none (2 const tables) | **BRIDGEABLE** |
| `_heapq` | `_heapqmodule.c` | 634 | 29 | 15 | 1 | 0 | none | none (3 const tables) | **BRIDGEABLE** |
| `_contextvars` | `_contextvarsmodule.c` | 66 | 16 | 4 | 0 | 0 | none | none | **SHIM** — see §2.1 |
| `binascii` | `binascii.c` | 1476 | 53 | 32 | 8 | 1 | none | none (const tables) | **BRIDGEABLE** |
| `_random` | `_randommodule.c` | 529 | 67 | 33 | 8 | 0 | one function | per-object (MT19937 in the object) | **BRIDGEABLE / STATEFUL** |
| `_struct` | `_struct.c` | 2121 | 137 | 76 | 14 | 3 | `f/d/e` codes only | `cache` dict (transparent memo) | **BRIDGEABLE, float-gated on 3 of 21 format codes** |
| `_json` | `_json.c` | 1715 | 144 | 97 | 12 | 0 | number parsing | none | **BRIDGEABLE-AT-THE-EDGE** — widest API per LoC, 60 gotos, C classes calling back into Python |
| `_sre` | `_sre.c` + `sre.h` + `sre_constants.h` + `sre_lib.h` | 3954 | 132 | 87 | 5 | 6 | none | none (init-only type objects) | **ENGINE** — the census's verdict stands; `sre_lib.h` is a backtracking VM compiled three times (UCS1/2/4 char widths) |
| `math` | `mathmodule.c` + `_math.c/.h` | 3293 | 101 | 70 | 16 | 23 | **173 mentions** | none | **FLOAT-GATED** (control confirmed; 23 libc math fns) |
| `_datetime` | `_datetimemodule.c` | 6030 | 189 | 143 | 29 | 9 | partial (`fromtimestamp`) | 27 statics, init-once caches | **BIG** — largest API of the field; not an engine, just a lot of it |
| `zlib` | `zlibmodule.c` | 1263 | 69 | 23 | 2 | 1 | none | 6 (incl. real flags) | **EXTERNAL-LIB** — the 23 semantic names are glue; inflate/deflate live in libz, which is NOT in this tree. Bridging the API buys nothing |
| `_socket` | `socketmodule.c` + `.h` | 7826 | 166 | 108 | 16 | 8+ | timeouts | real runtime state (`netdb_lock`, probe flags) | **EFFECT-CLASS** (control confirmed; §2.7 of the intrinsics memo, unchanged) |

`goto` density, the C-tier surface proxy: `_bisect`/`_heapq` 0,
`_struct` 4, `binascii` 5, `_random` 10, `math` 46, `zlib` 49, `_sre` 54,
`_json` 60, `_datetime` 63, `_socket` 89. The bridgeable core is
structured C; the engines are not.

### 2.1 The `_contextvars` surprise: it is a shim

`_contextvarsmodule.c` is 66 lines that re-export four symbols
(`PyContext_Type`, `PyContextVar_Type`, `PyContextToken_Type`,
`PyContext_CopyCurrent`). The implementation is `Python/context.c` —
1055 LoC, 114 API names, 30 of them internal, including the `_PyHamt_*`
family: a hash-array-mapped trie that is itself another interpreter
file (`Python/hamt.c`). "Execute `_contextvars` for real" therefore
means executing interpreter internals, not an extension module. The
intrinsics memo's name-only treatment (its pass 1) is not merely
cheaper here — it is the only version of `_contextvars` that is an
extension-module problem at all.

### 2.2 The internal-API tax

Every candidate except the two smallest leans on underscore-internal
CPython API: `_PyBytesWriter` (5 names, in both `_struct` and
`binascii`), `_PyAccu`/`_PyUnicodeWriter` (`_json`), `_PyFloat_Pack2/4/8`
(`_struct`), `_PyLong_AsByteArray` (`_random`, `_struct`),
`_PyTime_*`/`_PyOS_URandomNonblock` (`_random` seeding),
`_PyDict_SetItem_KnownHash` (`_sre`). A "bridge to the documented C
API" is a fiction for stdlib modules — they are in-tree code and use
in-tree private helpers. The bridge would have to model a slice of the
undocumented interior, version-pinned to 3.9.19, and every one of those
names is a claim with no upstream stability contract behind it.

## 3 The union curve

Greedy best-first over SEMANTIC names (boilerplate amortizes by
construction; semantic names are the real ledger), bridgeable-or-better
candidates only (controls excluded):

| add | new semantic | semantic union | full API union |
| --- | ---: | ---: | ---: |
| `_contextvars` | 4 | 4 | 16 |
| `_bisect` | +10 | 14 | 29 |
| `_heapq` | +11 | 25 | **41** |
| `_random` | +29 | 54 | 94 |
| `binascii` | +27 | 81 | 125 |
| `_struct` | +42 | 123 | 198 |
| `_sre` | +41 | 164 | 258 |
| `_json` | +55 | 219 | 324 |

**The first plateau is immediately after `_heapq`, and it is the only
plateau.** `_bisect`+`_heapq`+the `_contextvars` shim = 25 semantic + 16
boilerplate = **41 distinct API names**; the two real modules overlap
heavily (list access, `PyObject_RichCompareBool`, `Py_LT`, the same
error idioms) and neither touches floats, libc, buffers, or state.
After that the curve is close to linear: the 8 modules need 219 semantic
names against 354 counted separately — a 38% overlap that never deepens
as modules are added. Each new
module brings its own protocol neighborhood (buffers and bytes-writers
for `_struct`, unicode internals for `_json`, match-state objects for
`_sre`). There is no shared semantic core waiting to amortize; only the
boilerplate amortizes, and the intrinsics contract already priced
boilerplate at "a fixed pattern".

## 4 What it flips — joined against the import-ceiling census

Rule as in the intrinsics memo: a file is import-clean under executed
set S when its `strict_c` ⊆ S. Computed from
`docs/import-ceiling-census.json`, cumulative:

| executed set | newly import-clean | note |
| --- | --- | --- |
| ∅ + the pass-0 import forms | `bisect`, `opcode`, `quopri`, `stat` | PURE-ACCEL; no C needed, credited to nobody |
| +`_contextvars` | `contextvars` | import-only: actually RUNS |
| +`_struct` | `struct` | import-only: actually RUNS |
| +`_sre` | `sre_compile`, `sre_constants`, `sre_parse` | import+other: clean, not runnable (BitAnd, bytes literals, Set, DictComp, Nonlocal, class-creation, With, Delete — mostly the designed tail) |
| +`_heapq`, `_bisect`, `_json`, `binascii`, `_random`, `_datetime`, `math` — all seven together | **nothing** | every consumer's strict closure also needs `sys`/`builtins`/`_thread`/`_weakref` |
| all nine + the intrinsics memo's pass-2 (`sys`, `_locale` slices) | 17 total import-clean | = intrinsics' own 10 + the 4 pass-0 files + the `_sre` trio |

Two facts to hold onto. **First**: seven of the nine algorithmic
candidates — including every module the C route would execute most
convincingly (`_heapq`, `_json`, `binascii`, `_random`) — flip zero
files, because the ceiling is not them. The blocking set is
interpreter-kind (`sys` 140, `_weakref` 127, `builtins` 106, `itertools`
104, `_thread` 100), and those are not C algorithms one can execute —
they are the interpreter, which no C tier reaches either.

**Second, the decisive one: the C route's file-level exclusivity over
intrinsics is ZERO.** The only C-route flips beyond the intrinsics
memo's passes are the `_sre` trio — and their import-time use of `_sre`
was checked in the 3.9.19 `Lib/` sources: `sre_constants.py:18`
`from _sre import MAXREPEAT, MAXGROUPS`; `sre_compile.py:17`
`assert _sre.MAGIC == MAGIC`; `sre_compile.py:432`
`_CODEBITS = _sre.CODESIZE * 8`. Four CONSTANTS. A constant-slice
intrinsic (`MAGIC`, `CODESIZE`, `MAXREPEAT`, `MAXGROUPS` — the tier the
intrinsics contract already has) flips the same three files without
executing a line of C. Every file the C route makes import-clean,
name/constant intrinsics make import-clean too.

**What C execution buys that intrinsics cannot**, stated exactly: not
breadth but depth. (1) `struct.pack`/`unpack` computing real values,
`binascii` transcoding, `heapq`/`bisect` running the accelerated branch
— i.e. CALLS answering instead of refusing, which the sweep's file
metric cannot see because those calls happen in files still behind
other walls or in user programs. (2) The intrinsics contract's §2.5
accelerator-equivalence obligation discharged by construction — running
the same C CPython runs — instead of by differential assertion. (3) A
`re` engine, someday, for the 84 seeds whose closures carry `_sre` —
but that is the ENGINE row, priced at ~4000 LoC of backtracking VM, and
it still unlocks those seeds only alongside the interpreter-kind
modules it cannot supply.

## 5 Honest limits

- **The bridge models the API contract, not CPython internals.**
  Refcounting under the model's heap is a no-op by design (`Py_INCREF`
  spelled as identity) — sound while the C tier cannot observe
  refcounts, and `sys.getrefcount` stays out with the rest of `sys`.
  GC/`Py_VISIT` likewise. That decision is taken here so it is on the
  record, and it is falsifiable: any modeled module whose behavior
  depends on destruction order (none of the bridgeable core does) would
  expose it.
- **UB in the C tier = loud refusal.** Signed overflow, out-of-bounds,
  wild casts: the definitional C interpreter refuses rather than picks
  a meaning. This is the covenant's shape, and it is also work — a C
  tier that must DETECT UB is strictly harder than a compiler that may
  assume its absence.
- **Module-init boilerplate is a fixed pattern**, not general C:
  `PyModuleDef`/slot tables are static data a loader reads once. The 16
  boilerplate names of bridge v0 are that pattern, not 16 behaviors.
- **The static census reads all `#if` branches** (no preprocessor run),
  so counts are upper bounds — visibly so for `_socket`, whose Windows
  arms are counted. For the bridgeable core the slack is small; the
  verdicts do not turn on it.
- **The macro line is drawn at the identifier**, so `PyList_GET_ITEM`
  (a macro reading into the struct) counts one semantic name, same as
  the function form — fair for pricing the bridge, but it means "API
  name" ≠ "function call": some names are struct-layout claims.
- **`_PyArg_ParseTuple` format strings carry semantics** ("y*", "n",
  "O!") that the one-name argparse bucket flattens; the conversion
  behaviors largely coincide with number/buffer names already counted,
  but the format-string mini-language is its own small spec.
- **LoC is not effort**, and none of this prices the C definitional
  interpreter itself — declarations, pointers, structs, arrays, function
  pointers, `switch`/`goto` (0 in v0; 54-63 in the engines), the libc
  slice (0 names in v0; `memcpy`-class elsewhere). The per-module
  numbers say only what each module ADDS on top of that tier.

## 6 The numbers the decision needs

1. **Bridge v0** (`_bisect` + `_heapq` + the `_contextvars` shim): **41
   distinct API names** — 25 semantic, 16 boilerplate-by-pattern — over
   **912 LoC** of structured, libc-free, float-free, state-free C. It
   flips `contextvars` (runnable) and nothing else the intrinsics
   passes don't already flip.
2. **First module** (`_bisect`): 212 LoC, 20 API names (10 semantic),
   zero libc/floats/state/`goto` — the cheapest real C module that
   exists; flips 0 files by itself.
3. **Files**: import forms alone +4; C route +5 import-clean beyond
   that (`contextvars`, `struct` runnable; `sre_compile`,
   `sre_constants`, `sre_parse` clean-not-runnable) — **every one also
   reachable by name/constant intrinsics; C-exclusive file flips: 0.**
   The C route's actual product is execution depth (calls that answer,
   §4) and the §2.5 obligation discharged by construction, not sweep
   files.
4. Past v0 the curve is linear (~39 new semantic names per added module,
   reaching 219 at eight modules), the internal-API tax is unavoidable
   (§2.2),
   and the sweep ceiling stays where the census put it — at the
   interpreter-kind modules no third language reaches.

**This memo recommends nothing.** Adding a modeled language is a
covenant decision — the C tier would make claims about UB, about
internal CPython API, and about a heap it deliberately simplifies — and
that decision is the owner's. The price tag above is what the decision
is about; it is now measured, and it is owner-gated.
