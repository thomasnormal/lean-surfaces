# C intrinsics — the proposal (OWNER-GATED)

**Status: design memo, nothing here is built.** The import-ceiling census
(docs/import-ceiling-census.md, `docs/import-ceiling-census.json`)
established that the ceiling on "verify arbitrary Python" is C extension
modules: of the 154 stdlib files refusing with `import`, 0 have pure
closures and 150 are C-BLOCKED. Whether to model C modules as Lean
intrinsics is a covenant question — a modeled module is a claim about
code this project cannot read — and the decision is the owner's. This
memo exists to make that decision DECIDABLE: it ranks the targets from
the census's own rows, states the contract a modeled module would have
to satisfy, prices the first candidates by what their consumers actually
touch, and says plainly what the work does not buy.

Every number below is recomputed from `docs/import-ceiling-census.json`
(the per-file STRICT closures — accelerators failed, fallbacks followed
— which is the branch a Python-only interpreter runs) and from the
pinned 3.9.19 sources. Nothing is quoted from memory.

## 1 Ranked targets, from the data

### 1.1 Blocking degree (how often a C module appears in a strict closure)

41 distinct C modules appear in the 150 C-BLOCKED strict closures
(62 was the census's FULL-scope count; STRICT is narrower because
accelerator-only C never runs). The top of the frequency list:

| C module | degree (of 150) | | C module | degree |
| --- | ---: | --- | --- | ---: |
| `sys` | 140 | | `_io` | 76 |
| `_weakref` | 127 | | `time` | 40 |
| `builtins` | 106 | | `math` | 29 |
| `itertools` | 104 | | `_struct` | 22 |
| `_thread` | 100 | | `marshal` | 22 |
| `posix` | 88 | | `errno` | 21 |
| `_sre` | 84 | | `_imp` | 20 |

Frequency is the WRONG ranking, as the census already warned: a file
unlocks only when its ENTIRE strict C set is covered (its pure closure
members are the module system's job, not this proposal's). The set
cover is the real price list.

### 1.2 The greedy cover — with its metric stated honestly

Rule: a file counts as UNLOCKED under a modeled set S when every module
in its `strict_c` is in S. (A guarded accelerator whose module lands in
S stops raising `ImportError` and takes its body branch instead; since
every accelerator body in these closures is `from _mod import …` of the
module itself, S covers that branch too, so the rule is exact for this
corpus.) Unlocked means IMPORT-CLEAN — the `import` wall falls — not
that the file runs: 143 of the 150 also carry other walls.

| picks | module added | newly import-clean | cumulative |
| ---: | --- | ---: | ---: |
| 1 | `sys` | 7 | 7 |
| 2 | `_weakref` | 5 | 12 |
| 3 | `posix` | 10 | 22 |
| 4 | `_sre` | 3 | 25 |
| 5 | `itertools` | 3 | 28 |
| 6 | `_io` | 2 | 30 |
| 7 | `builtins` | 3 | 33 |
| 8 | `_thread` | 31 | 64 |
| 9 | `_struct` | 6 | 70 |
| 10 | `time` | 4 | 74 |

Three facts the curve carries. (1) `_thread` is the sleeper: degree 100
but worthless alone; once the seven modules it co-occurs with are in, it
unlocks 31 files at a stroke. (2) `posix` at pick 3 is the by-kind
boundary wearing a good rank — its ten files are the `os.path` family,
and modeling `posix` is inventing an operating system; the pick is
listed because the greedy found it, and it is declined below. (3) The
census's unresolved residue (`nt` in 88 rows, `os.path` in 87) is a
STATIC artifact — both sides of `os.py`'s platform `if` were walked, and
`os.path` has no source file to resolve to — which execution dissolves:
leanpy RUNS a module-level `if`, so only the `posix` branch would ever
be demanded. It blocks nothing here.

### 1.3 The bucket that actually moves the sweep

The sweep metric counts whole files, and only the import-only bucket
can flip when imports land. It has 8 files: `bisect` (PURE-ACCEL — no
intrinsic needed, the guarded-form fallback admits it) and 7 C-BLOCKED.
Their strict C sets, smallest first:

| file | strict C set | flip verdict (checked against 3.9.19 source) |
| --- | --- | --- |
| `contextvars` | `_contextvars` | **FLIPS with a name-only intrinsic.** The file is two statements: a `from`-import of 4 names and an `__all__` tuple. Nothing imported is ever used at top level. |
| `struct` | `_struct` | **FLIPS with a name-only intrinsic.** `__all__` list, `from _struct import *`, two more `from`-imports. Star-import needs the pinned export table; nothing is called. |
| `_bootlocale` | `_locale`, `sys` | PLAUSIBLE, with listed costs: `sys.platform` (a pinned constant), `str.startswith` (NOT in the str tier today), `_locale.CODESET` under `try/except AttributeError`. |
| `reprlib` | `_thread`, `builtins`, `itertools` | Blocked past imports: its last line `repr = aRepr.repr` binds a bound method as a VALUE — loud in the class tier. Three intrinsics buy nothing until that lands. |
| `decimal` | 8 modules | Out of range. |
| `sitecustomize` | 8 modules | Out of range. |
| `pipes` | 14 modules | Out of range. |

Greedy over this bucket: **1 module (`_contextvars`) flips 1 file; 2
(`+_struct`) flip 2; 4 (`+sys,_locale`) flip 3.** That — plus `bisect`
for free — is the entire direct sweep payoff of the intrinsic idea.

### 1.4 The compound with the designed tail

The import+other files an intrinsic makes import-clean still refuse on
their other walls — but some of those walls are tail constructs already
designed or staged. With S = `{_contextvars, _struct, sys, _locale}`,
10 files are import-clean; of these, `symbol` retains only `Delete`
(designed) plus a live `globals()` call the walls census cannot see
(its `sym_name` loop iterates `globals().items()` — a builtin the one
pipeline could answer exactly, since the module frame's locals ARE its
globals, but it is not modeled today); `codeop` retains `BitAnd`
(designed) and `With`; `formatter` retains `Delete`, `Starred`
(designed) and class-creation. So the compound is real but arrives only
as the tail batch lands — no import+other file flips on intrinsics
alone.

### 1.5 What the data surprised us with

The by-kind verdict ("`sys` cannot be modeled without inventing the
interpreter") is TRUE OF THE MODULE and FALSE OF THE SLICE. Whole-file,
the C-BLOCKED corpus touches 63 distinct `sys` names across 114 files;
at IMPORT TIME, the 7 files that `sys` alone would make import-clean
touch exactly THREE: `sys.implementation`, `sys.exc_info` (the
`types.py` raise-and-capture trick — genuinely reflective, stays loud),
and `sys.warnoptions`. The unit that decides modelability is the NAME,
not the module — which is exactly how the interpreter already treats
`time` (only `time.time()` pops the trace clock) and `builtins` (per
name, `isPyBuiltinName`). The second surprise is §1.3 itself: the two
modules that flip sweep files, `_contextvars` (degree 1) and `_struct`
(degree 22), are nowhere near the top of the frequency table, and the
top of the table flips nothing.

## 2 The intrinsic contract

What "modeling a C module" means under this repo's covenant. Normative;
each clause has a falsification obligation.

**2.1 The pinned inventory.** A modeled module's surface is `dir(M)` of
the pinned interpreter (CPython 3.9.19, Homebrew), captured by
subprocess like the census's C-module table, committed as data, never
imported at build time. This is the `isPyBuiltinName` precedent: the
inventory exists so that NO absence is ever guessed.

**2.2 Per-name admission, four member tiers.** Each name in the
inventory is one of:

| tier | meaning | precedent |
| --- | --- | --- |
| CONSTANT | an in-tier `RVal`, pinned against the interpreter (`_locale.CODESET`, `sys.platform`, `errno.EINVAL`, `_sre.MAXREPEAT`) | the cast tier's pinned answers |
| FUNCTION | a pure Lean function on `RVal`s with faithful errors (`math.gcd`; `_struct.calcsize` once a bytes tier exists) | `str`/`int` builtins |
| STATEFUL | state as a DECLARED input, never hidden — a trace (`time.time`) or a seed (`_random.Random` is deterministic given its seed) | the trace clock, pass 6 |
| OPAQUE | the import BINDS a value; every use of it — call, attribute, operator, `print` — refuses loudly | instances refuse `repr`; bound-method values are loud |

OPAQUE is the load-bearing novelty, so its soundness argument is stated:
binding an opaque value is observationally safe because the tier can
already hold values it refuses to observe (instances, closures);
identity against it is never claimed, rendering it refuses, and the
first use is a loud stop. CPython binds a different value — but no
program the model DECIDES can tell. A name in the inventory but in no
tier is OPAQUE-at-import and loud-at-attribute-read; it is never
skipped and never faked.

**2.3 The loudness rule.** An unmodeled attribute of a modeled module
refuses loudly — never a fake `AttributeError`, because the real module
HAS the attribute. A name genuinely absent from the pinned inventory
answers the faithful `AttributeError`, and that claim is only as good
as the inventory, which is why the inventory is captured from the
interpreter and not typed by hand. This is the same split
`isPyBuiltinName` enforces for `NameError`.

**2.4 Interaction with the import forms.** The census found the paying
forms narrow, and intrinsics widen them by exactly one: absolute
`from X import names`, `from X import *` (star reads the pinned export
table — `__all__` if the module defines one, else the underscore-free
inventory, CPython's own rule), and plain `import X` binding a
module-object value whose attribute reads go through §2.2. No dotted
packages, no relative imports — the corpus never pays for them. A
module NOT modeled and not on disk raises a catchable `ImportError`
inside a `try/except ImportError` guard (that is what admits the four
PURE-ACCEL files) and refuses LOUDLY when unguarded — an unguarded
missing module is a `ModuleNotFoundError` claim, and we make it only
where the pinned platform inventory backs it.

**2.5 The accelerator-equivalence obligation.** Running a PURE-ACCEL
file means running its pure fallback where CPython 3.9.19 runs the C
accelerator. The admission therefore ASSERTS observational equivalence
of the two branches on everything the tier can see. That assertion is
not taken from the docs: every such file gets differential battery rows
exercised through the fallback against CPython running the C module,
and any divergence — a message, a type, an edge case — is a blocker,
not a footnote.

**2.6 Differential testing.** Every modeled name in CONSTANT, FUNCTION
or STATEFUL tier gets battery rows in `harness/cases.json` /
`harness/scripts/` against pinned CPython 3.9 before its first use in a
proof, like every builtin before it. OPAQUE names get REFUSAL rows —
the row that proves the loud path is loud.

**2.7 What is OUT, by kind.** Modules whose semantics are EFFECTS, not
functions: `_thread`/threading (a scheduler), `posix`/`os` process
state, `_socket`/`select` (the network), `_io` (file descriptors),
`_imp`/`marshal`/frame reflection (`sys._getframe`, `sys.modules` as a
mutable registry, `sys.exc_info` frames). These stay out as SEMANTICS;
§2.2 still allows their constant slice (an `errno` number, `sys.platform`)
and their opaque bindings (`_thread.get_ident` bound but never callable)
— the boundary runs through names, not through module files.

## 3 Cost shape, per candidate

Measured by grepping what the refusing files and their pure closure
members actually touch (AST walk over the census closures; import-time
= module body and class bodies, excluding `def`/`lambda` bodies), not
by the module's full API.

| candidate | names touched (whole corpus / import-time by its unlock set) | tier landing | the design question |
| --- | --- | --- | --- |
| `_contextvars` | 4 / 0 used | all OPAQUE | none — `contextvars.py` only re-exports. A REAL `ContextVar` is mutable heap state (an `Obj`, the dict-tier shape) — a later, separate design. |
| `_struct` | 11 exports / 0 used | all OPAQUE now; `pack`/`unpack`/`calcsize` are FUNCTION-tier once `Constant:bytes` (designed) gives them a value to return | none for the flip; the bytes dependency is the whole later cost |
| `sys` | 63 whole-file / 3 import-time | `platform`, `maxsize`, `version_info`, `warnoptions`, `implementation` CONSTANT; `argv` is already a marshalled boundary global by precedent; `stdout`/`stderr` could one day meet `World.stdout`; `modules`, `_getframe`, `exc_info`, `settrace` OUT §2.7 | none of the three import-time names blocks the wrong side: 2 constants + 1 refusal |
| `_locale` | 3 / 1 (`CODESET`) | CONSTANT | none |
| `errno` | 27 / — | all CONSTANT | none; pure unlock synergy, no file needs it alone |
| `math` | 23 / — | all FUNCTION over floats | the float tier does not exist; declined until it does |
| `itertools` | 11 / 3 (`islice`, `chain`, `repeat`, … ) | FUNCTION as generator frames — `count` is ALREADY modeled this way | cheap by kind, but unlocks only inside the big batch |
| `_sre` | 9 / 9 | `MAGIC`/`MAXREPEAT`/… CONSTANT, but `compile` is a regex ENGINE returning stateful match objects | declined — the census already priced "a Lean regex engine" as its own project |
| `_random` | — | STATEFUL, seedable — the trace-clock template exactly (deterministic given seed; OS entropy stays out) | the template exists; no file in this corpus pays for it yet |

## 4 Recommendation

**Pass 0 — no intrinsics at all: the import forms.** `from X import
names`/`*` under `try/except ImportError` with the §2.5 obligation
admits `bisect` — the census's one program-mode flip — and is a
prerequisite of everything below. Build first regardless of the gate.

**Pass 1 — `_contextvars` and `_struct`, name-only (RECOMMENDED).**
Two modules, zero modeled semantics, entirely OPAQUE members plus the
pinned export table. Measured payoff: `contextvars` and `struct` flip
outright (§1.3 — verified against their 3.9.19 sources, which bind and
never use). More than the 2 files, this pass is the cheapest possible
end-to-end exercise of the WHOLE contract — inventory, module-object
value, star-import, opaque binding, loud attribute, refusal rows — on
files where nothing can hide.

**Pass 2 — `sys` as a constant slice, plus `_locale.CODESET`
(RECOMMENDED IF pass 1 holds).** Pinned constants only (`platform`,
`maxsize`, `version_info`, `warnoptions`); everything else loud per
§2.3. Flips `_bootlocale` once `str.startswith` lands (a small,
separately arguable str-tier addition), makes 7 more files
import-clean, and converges with the designed tail: `symbol` then
retains only `Delete` plus a `globals()` builtin the one pipeline could
answer exactly, `codeop` only `BitAnd` + `With`.

**Declined, with the reason on record:** `posix` (greedy pick 3 — ten
files, all of them the os-path family; modeling it is inventing an OS,
§2.7), `_sre` (a regex engine), `math` (no float tier), everything
STATEFUL until a file pays for it.

**What this does NOT buy.** The sweep counts whole files, so the
honest total for passes 0-2 is **+3 to +4 files of 154** (`bisect`,
`contextvars`, `struct`, then `_bootlocale`) — the C-BLOCKED headline
moves from 150 to ~146, and no import+other file flips without the
tail batch it was already waiting for. The greedy curve's far end (8
modules → 64 import-clean) is NOT on offer here: those 64 are
import-clean, not runnable, and the modules that get there include the
§2.7 exclusions. The library tail (208 modules, class-creation at 127)
is untouched by any of this and remains the larger lever.

**The same effort spent elsewhere.** The f-strings tail batch is
already staged and moves ordinary language surface; per-file VALUE
comparison (comparing computed results, not just stdout/exit) deepens
every existing MATCH. Either is a defensible alternative; the argument
for pass 1 anyway is that it is small (two files' worth of contract
machinery), measured, and settles by construction whether the intrinsic
contract is livable before anything expensive is built on it.

**The three questions the owner is actually deciding**, separated so
they can be answered separately:

1. Is OPAQUE binding within the covenant — may the model bind a value
   CPython binds differently, given every observation of it refuses?
   (§2.2; pass 1 stands or falls here.)
2. Is accelerator-fallback equivalence, differentially tested, an
   acceptable claim? (§2.5; `bisect` and pass 0 stand or fall here.)
3. Is modelability decided per NAME rather than per MODULE — i.e. may a
   constant slice of a by-kind module be modeled while the module's
   effects stay out? (§2.7 vs §1.5; pass 2 stands or falls here.)

A "no" on any of the three is a complete answer: the corresponding pass
is dropped and the ceiling stands as measured, 4/154.
