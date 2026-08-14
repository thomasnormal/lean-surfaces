# Backlog

This file records deliberately deferred platform work. Items here are not
implemented features and must not be described as part of the current proof
surface.

## Verilog-AMS

Full Verilog-AMS support is deferred. The active analog HDL frontend is the
OpenVAF-backed Verilog-A subset.

Before Verilog-AMS work resumes:

1. Select and pin a third-party frontend that parses and elaborates the
   required Verilog-AMS standard. Slang/pyslang covers SystemVerilog, not the
   analog Verilog-AMS grammar; it is not an AMS frontend.
2. Project the frontend's typed AST into the shared circuit IR. Do not add a
   handwritten fallback parser.
3. Elaborate natures, disciplines, analog/digital ports, connect modules, and
   automatic connection-module insertion with explicit rejection of
   unsupported constructs.
4. Give analog events and digital delta cycles a unified superdense-time
   semantics, refining the existing continuous DAE semantics and SV
   scheduler rather than replacing either.
5. Prove frontend projection and mixed-signal composition theorems, including
   non-vacuity and model-domain invariance.
6. Add conformance and differential tests against an independent
   Verilog-AMS implementation.

The existing frontend-independent sampled analog/SV relation is useful
infrastructure, but it is not a Verilog-AMS source frontend or execution
semantics.

## Python tier: `leanpy` — the script runner (owner-directed, 2026-08-06)

A `leanpy file.py` binary that extracts, ingests, and interprets ARBITRARY
Python files under the Lean semantics. Rationale (recorded verbatim from
the direction): (1) it generalizes the differential harness from typed
function calls to whole programs — stdout + exit code against the pinned
CPython 3.9; (2) it turns the completeness goal into an empirical metric —
run corpora (eventually CPython's own test suite), report the fraction
completing and WHICH construct blocked each failure, so loudness becomes
telemetry that prioritizes the ladder; (3) the end-state demo: sunfish.py
playing identical chess under `leanpy` vs CPython — an executable fidelity
check closing the hand-transcription gap for the whole sunfish effort.

Design already fixed in the H1 core (docs/memory-model.md §effects):
stdout is `World` data (`World.stdout`), exit status is a runner-boundary
mapping, argv a marshalled global.

**v0 is BUILT (2026-08-07):** `leanmodels-run --script <envelope.json>`
(LeanModels/Python/Script.lean) executes a module's top level in one
world with `print` intercepted at statement position (scalar `str()`
tier), exit codes ok→0 / exn→1(+class line on stderr) / unsupported→3 /
timeout→4 — the loud codes are never agreement; the differential side is
`harness/script_corpus.py` over `harness/scripts.json` (stdout + exit
code vs the pinned CPython, first-unsupported-construct telemetry — 10
scripts: 7 matched, 3 loud-blocked at corpus creation). Consistency
architecture: the G1-FAITHFUL PREFIX (plain binds/docstrings) is skipped
by the live run — its effects, dict identities included, are already in
`initWorld` — and the live SUFFIX executes with control shells for
`while`/`if` (prints inside loops work); loud refusals: a def after live
code, a suffix rebinding of a table-bound name some function reads, and
in-function `print` (the interpreter also gained two soundness fixes v0
surfaced: post-boundary G1 bindings are POISONED, never stale, and
in-function `print` is loud rather than a wrong `NameError` —
`Examples/python/g1_lab` rows pin both). The ordered `ModuleItem`
representation remains the recorded fix for everything the boundary
refuses. Next per the direction: grow the corpus (eventually CPython's
own test suite) with telemetry prioritizing the ladder (H2 lists, H3
classes, H4 generators); sunfish-under-leanpy stays the capstone (likely
post-H4). A single-call convenience driver (`tools/lean-python`: extract
→ `leanmodels-run`, with an optional one-off CPython comparison) also
exists.

**v1 — THE BINARY AND THE METRIC — BUILT (2026-08-12).** The two things
the direction actually asked for, both landed:

* `tools/leanpy <file.py>` is the binary. It extracts an ARBITRARY file
  (`extract.py --out`, envelope cached by source sha256 under
  `$TMPDIR/leanpy-cache`, nothing written next to the source — so a
  read-only tree or someone else's project can be run), then executes the
  module's whole top level under the interpreter with stdout and exit
  status forwarded verbatim: a drop-in for `python3 file.py` on the
  supported fragment. Exit codes 0/1/3/4 as v0, plus 5 for a `--compare`
  disagreement and 2 for a usage/extraction failure; `--clock i,j,k`
  seeds the trace clock (this CLOSES the pass-6 script-mode trace-flag
  deferral — `runScript` is now `runScriptClock m []`). It uses the built
  `.lake/build/bin/leanmodels-run` (a `lake` invocation costs ~9 s of
  olean replay) and says so LOUDLY when that binary is older than a Lean
  source, rather than reporting a stale answer.
* `harness/leanpy_survey.py` is the metric. Point it at a corpus file of
  named groups (`harness/leanpy_corpus.json`) or at paths/globs, and
  every file lands in exactly one of MATCH / DIVERGE / REFUSE / TIMEOUT /
  ORACLE / EXTRACT / HUNG. The model side is ONE
  `leanmodels-run --script-batch` process for the whole corpus (the
  standing batch rule: 167 files cost 1.5 s of model time, not 167 lake
  startups); the oracle side defaults to the PINNED `python3.9` when
  installed, and its version is printed with every report, because
  surveying against a newer python3 would report version drift as model
  divergence. Two telemetry layers, answering different questions: the
  DYNAMIC refusal message (what stopped real programs first) and the
  STATIC `Unsupported`-node census by `py_kind` (what the files contain
  — the ladder's priority queue). Every run also reports `live`, the
  number of live-suffix statements the executor was given, so a
  definitions-only agreement is never dressed up as a real run.

MEASURED, 2026-08-12, oracle CPython 3.9.19:

* in-repo corpus (`harness/leanpy_corpus.json` — 20 corpus scripts, 51
  Examples sources, the 8 vendored `Lib/test` files): **79 files, 57
  MATCH (72.2%), 22 REFUSE, 0 DIVERGE**. Of the 57, **15 executed live
  top-level statements and printed CPython-identical output**; the other
  42 are definitions-only modules (`live = 0`) that ingest, module-
  initialize and finish silently.
* THE WILD SWEEP — 167 real CPython 3.9 stdlib modules
  (`lib/python3.9/*.py`, minus a seven-name safety list whose top level
  opens a browser or a window): **9 MATCH (5.4%), 158 REFUSE, 0
  DIVERGE** — and all 9 are `live = 0`, so the honest statement is that
  ZERO stdlib files execute live top-level code under the model today,
  nine ingest and initialize, and nothing lies. Static census over the
  same 167: 275058/279327 = 98.5% of extracted AST nodes are in tier (an
  UPPER BOUND — an `Unsupported` node is a leaf and hides its subtree).

WHAT THE TELEMETRY DECIDES (the point of building it): the top dynamic
blocker is not a language construct at all — it is leanpy's OWN
`defsBeforeLive` boundary, **146 of the 158 stdlib refusals and 17 of the
22 in-repo refusals**. The recorded fix, the ordered `ModuleItem`
representation, is therefore no longer one deferred idea among many: it
gates 92% / 77% of everything that refuses, and it is the next leanpy
milestone. Behind it the static ranking gives the ladder: `Import` (886
nodes / 142 files), `Constant:bytes`, `ImportFrom`, `With`,
`BinOp:BitAnd`, `ListComp`, `Constant:float`, `JoinedStr`, `Assert`,
`Starred`, `Delete`, `Lambda`.

FIRST BUG FOUND BY THE INSTRUMENT (2026-08-12, same day, fixed): pointing
leanpy at `class C: print("x")` produced a MISMATCH, not a refusal —
CPython runs a class body at the `class` statement, the model builds
`ClassDefn` at ingestion and executes no class body, so the print
vanished. `class C(base())` is the same hole through the other door.
Closed loudly: `ClassDefn.creationPure` + `runScript`'s
`classesCreationPure` admission (docs/memory-model.md §class semantics,
"Class CREATION is an effect"), pinned by
`harness/scripts/cls_effect_script.py` (the refusal) and
`cls_data_script.py` (a creation-pure class still runs, and stays
uninstantiable — the two flags are independent).

**THE ORDERED ADMISSION — BUILT the same day (2026-08-12), and the
telemetry it produces is a different ladder.** The blanket rule "every
definition precedes all live code" was the top blocker; it is replaced by
`defsBoundBefore` (Script.lean): a top-level statement may mention a name
the module binds by `def`/`class`/namedtuple only if that definition ENDS
before the statement begins. The model's position-independent tables and
CPython's sequential binding then agree on every reference actually made,
and a genuine forward reference — where CPython raises `NameError` — still
refuses loudly. The check covers ALL of `topLevel`, not just the live
suffix, which closes a SECOND silent hole: `x = f()` above `def f` sits in
the G1 prefix, the old rule never looked there, and the model answered `1`
where CPython exits 1 with `NameError`
(`harness/scripts/prefix_forward.py` pins it; `interleave_script.py` is
the payoff row, `call_before_def.py` the unchanged refusal).

RE-MEASURED after both changes (same corpora, same 3.9.19 oracle):

* in-repo corpus, now 83 files (four new rows): **58 MATCH (69.9%), 25
  REFUSE, 0 DIVERGE**, 17 of the matches executing live top level. The
  percentage moved DOWN from 72.2% and that is the honest direction: 20
  files used to "match" only because the model silently skipped their
  class bodies.
* stdlib sweep, same 167 files: **8 MATCH, 159 REFUSE, 0 DIVERGE**.

And the refusal ladder is now made of real constructs instead of one
structural artifact — the def-ordering refusal collapsed from 146 files to
1:

| files | what actually stopped the run |
|---|---|
| 108 | class CREATION effects (inheritance, computed class attributes, decorators) |
| 27 | live top-level code rebinds a module global some function reads (`suffixConsistent`) |
| 12 | `import` |
| 5 | `except ImportError:` (an unadmitted exception class) |
| 1 each | forward reference, `.join`, `.extend`, namedtuple class as a value, `try/else` |

sunfish.py's own refusal moved with it: it now clears ingestion, class
creation and the ordering check, and stops at `suffixConsistent` — the
module-init `pst` store into a name its functions read — which is a named
condition about THIS program, not a boundary artifact.

**`__name__` SUPPLIED (2026-08-12, third leanpy change of the day)**: the
`if __name__ == "__main__":` guard — the shape essentially every runnable
Python file is wrapped in — was unreachable because reading `__name__`
refused. It is now the first MARSHALLED GLOBAL of the runner boundary
(docs/memory-model.md §effects), script-mode only. In-repo corpus 84
files: 59 MATCH (70.2%), 25 REFUSE, 0 DIVERGE, 18 executing live top
level. The stdlib sweep is unchanged at 8 MATCH: those files' blockers
come earlier.

**TWO MORE SILENT DIVERGENCES, FOUND AND GUARDED (2026-08-12)**: module
initialization rolls back a top-level statement it cannot execute, and for
a whole program that statement's own effect is observable — `x = talk()`
with a printing `talk` lost the output, and `x = 1 // 0` lost the
exception AND the exit code. Both were WRONG ANSWERS, not refusals.
`initNothingSkipped` (docs/memory-model.md §module-init execution) now
refuses such a program, with the residue (a failed binding masked by a
later successful rebinding of the same name) recorded rather than
accepted. Cost, honestly: the stdlib sweep fell from 8 MATCH to 5 — three
of those files had a rolled-back init statement and were only matching
because the guard did not exist. In-repo corpus unchanged at 59/84.

THE STANDING SHAPE OF THIS BUG CLASS: leanpy runs a program through TWO
pipelines — the G1 fold for the prefix, the script executor for the live
suffix — and every hole found so far is a place where the fold's
approximation (skip, poison, never print) meets the program surface's
demand (every effect observable, in order). The recorded end state is ONE
pipeline: execute every top-level statement through the executor, with
module-level bindings written to the live globals and read back through
the poisoned arm. That subsumes `initNothingSkipped`, the residue above,
and the `suffixConsistent` wall (27 stdlib files, and sunfish.py itself —
measured: sunfish's live suffix opens at the pst padding loop on line 78,
so all 22 constants defined after it are "assigned by live code and read
by functions"). It is the next leanpy milestone and it is a DESIGN, not a
patch: function frames resolve module names statically-first, so the
unification has to answer how a live binding becomes visible to a call
without breaking the world-symbolic covenant that keeps theorems provable.

**THE ONE PIPELINE — BUILT (2026-08-13), docs/memory-model.md §the one
pipeline.** The split is gone. `runScript` executes EVERY top-level
statement through the script executor, from an empty world, publishing
the frame's locals as `World.globals` after each statement (CPython's
module frame, whose locals ARE its globals); `initWorld` is never called
in script mode. The covenant is kept by not touching resolution at all —
the threaded module VIEW (`scriptView`) carries no program statement, so
every module global is statically ABSENT and the absent arm's live-view
consult decides, which makes sequential visibility exact for free. The
view keeps exactly three things: `__name__` (the dunder arm fires before
the live consult), an unnameable top-level `def` (so `topLevelDefFree` is
false and closure calls take their dynamic path), and the module's import
statements (so the benign whitelist still poisons `time` and
`moduleClockOk` still holds). DELETED, not tightened:
`initNothingSkipped` (and its recorded residue), `suffixConsistent`,
`g1Shape`/`g1Prefix`/`liveSuffix`. The one narrow residue left is
`scriptFlushCoherent`: a compound statement DELEGATED wholesale to
`execStmt` (`for`, `try`, `while … else`) holds its bindings until it
ends, so a name it assigns may not be one a function body reads — the fix
is a control shell per statement kind, and the executor already has `if`,
`while`, and the `for … in d.items():` shell that module-init execution
used to own.

MEASURED (same corpora, oracle CPython 3.9.19): in-repo **69/86 MATCH
(80.2%), 0 DIVERGE**, up from 59/86 (68.6%) — and the honest half of that
number, files that actually EXECUTED live top-level statements, went
**18 → 47**. `harness/script_corpus.py` went 18 matched / 9 loud →
**21 matched / 6 loud**, with three refusal rows flipping to
CPython-identical answers (`live_rebind_read.py` and
`live_fresh_global.py`, renamed from `suffix_*` because they are payoff
rows now, and `init_raise_script.py`, where the top-level `1 // 0` now
propagates to exit 1 instead of being rolled back). `sf_order.py` — the
sunfish ordering arc — went REFUSE → MATCH with 11 live statements.

THE WILD SWEEP, same 167 stdlib modules, same 3.9.19 oracle: **5 MATCH,
162 REFUSE, 0 DIVERGE** — the count is unchanged, and the qualitative
statement behind it is not: **4 of the 5 now EXECUTE live top-level
statements**, where before the pass all of them were `live = 0` and the
honest statement was that ZERO stdlib files executed live top-level code
under the model. The refusal ladder lost its structural entry entirely —
the 27 `suffixConsistent` files are gone — and is now made of constructs:

| files | what stopped the run |
|---|---|
| 108 | class CREATION effects (inheritance, computed class attributes, decorators) |
| 36 | `import` / `from … import` |
| 5 | `except ImportError:` (an unadmitted exception class) |
| 4 | a delegated compound binds a function-read name (`scriptFlushCoherent`) |
| 2 | `try/else` |
| 1 each | `dict + dict`, `BinOp:Div`, `Set`, `DictComp`, `frozenset`, a forward reference, a namedtuple class as a value |

And sunfish.py's own refusal moved from an architectural wall to ONE
NAMED CONSTRUCT — `opt_ranges = dict(QS=(0, 300), …)`, the unmodelled
`dict` builtin. Everything before it now RUNS: ingestion, class creation,
the ordering admission, and the pst padding loop through the items shell.

TWO BUGS THE UNIFICATION EXPOSED, both reachable BEFORE it on the
closed-function surface:

* **An unmodelled CPython builtin answered `NameError` — a WRONG ANSWER
  (FIXED).** sunfish.py's `opt_ranges = dict(QS=(0, 300), …)` resolved
  `dict` through every arm and fell out as a faithful-looking `NameError`;
  `def f(): return len(dict())` did the same from an ordinary function
  body. `isPyBuiltinName` (Semantics.lean) is now the full
  `dir(builtins)` of the pinned CPython 3.9, consulted by every arm that
  may DECIDE a `NameError`, and an unmodelled builtin is a loud refusal
  naming the construct.
* **`moduleGenFree` claimed more than it can — FIXED (2026-08-13).** Its
  docstring said no `Obj.generator` can exist in a module with no
  generator defs because "`callIn` is the only allocator" — but
  `enumerate(…)` and `itertools.count(…)` allocate generator frames with
  no generator def in sight, so `for i, c in enumerate("PNB"):` in such a
  module refused with `internal: … heap well-formedness violation —
  report this`: ordinary Python reported as an interpreter bug, reachable
  from a plain function body too. Loudness defect, not soundness —
  `Expr.heapFree` already excludes `enumerate`/`count`/`next` calls, so
  `worldInv` never met the arm. `moduleGenFree` now also requires
  `genAllocFree` over the function bodies AND the top level; the walkers
  are LIST-recursive because `Module.heapFree` is discharged by `rfl` and
  `Array.all` does not reduce in the kernel. No example lost `heapFree`.
  Acceptance: `iter_lab.enum_sum`/`enum_first` (a module with no
  generator def of its own, plus `#guard !moduleGenFree iter_lab`) and
  `harness/scripts/enum_script.py`.

**`print` IS AN ORDINARY BUILTIN (2026-08-13)** — docs/memory-model.md
§`print` is an ordinary builtin. The oldest leanpy deferral ("the effect
must thread the mutual block") is closed: `evalExpr`'s call arm appends
to `World.stdout` and returns `None`, after every shadow-resolving arm,
so `print` works in a function body, in a nested call, and inside any
statement leanpy delegates — the executor stopped intercepting `print`
entirely, which also removed the "prints inside a top-level `for` are
loud" gap. `print` leaves `Expr.heapFree` (the first world-mutating
non-allocating expression), and the three proof obligations moved with
it: `worldInv` gains `hprx`, `fuelMono`'s branch becomes a `bind`,
`clockErase` gains a `bprint` case closed by `of_seed`. RECORDED: the
VALUE boundary does not observe stdout — `callFunction` drops the world,
so `CallsTo` is silent about output and `CallsIn` (or the script surface)
is where it is seen. In-repo corpus **72/87 MATCH (82.8%)**, 0 DIVERGE;
script corpus 24 matched / 4 loud, `fnprint.py` and
`init_effect_script.py` flipping to CPython-identical output.

**LIST COMPREHENSIONS ARE LIVE (2026-08-13)** — docs/memory-model.md
§list comprehensions. `ListComp` was the top in-repo construct on the
static ladder. The extractor emits it as the SAME node as a generator
expression under a different `kind`, INGESTION desugars it into
`list(<the genexp>)` (CPython's own compilation — the `yield from`
inlining precedent), and the whole genexp lowering carries over: capture
census, walrus filter, drain gate. The only new interpreter piece is the
`list(iterable)` CONSTRUCTOR — `tuple`'s inventory with an allocation, so
it leaves `Expr.heapFree` and its generator arm drains without the
`moduleGenFree` guard. In-repo corpus **73/88 MATCH (83.0%)**, 0 DIVERGE;
998 differential cases, 0 failed. RECORDED as the next visible wall in
its place: `print` of a CONTAINER (a list's `repr` is not guessed —
`harness/scripts/print_container.py`).

**CONTAINERS RENDER (2026-08-13)** — docs/memory-model.md §rendering.
`print` now applies CPython's two-level rule (`str()` on the arguments,
`repr()` inside a container): str quoting and escapes, the one-element
tuple's comma, namedtuple `field=value`, dicts in insertion order, range
with its step elided at 1, and `[...]` for a self-referential container,
decided by an active-path list rather than fuel. LOUD and pinned: a set
(hash order), an instance/closure/generator (identity), a non-ASCII
string (Unicode printability is never guessed). `repr_script.py` is the
differential row; `print_set.py`/`print_nonascii.py` the refusals.

**`dict(…)` — AND THE SHIPPED FILE'S WHOLE TOP LEVEL (2026-08-13)** —
docs/memory-model.md §the `dict(…)` constructor. `dict()`, `dict(k=v, …)`
in call order, and `dict(d)` as CPython's shallow copy; a pairs iterable
stays loud (the per-insert hashability and duplicate-key rules are not
guessed). It was sunfish.py's last named blocker, so `runScript` now
executes the REAL engine file's entire top level — imports, tables,
padding loop, namedtuples, class creations, the `__main__` guard — and
stops only at `main()`'s `import sys, sunfish_ui.uci`, which is out of
scope BY KIND and which CPython does not survive either
(`ModuleNotFoundError`). Pinned by message in
`Examples/python/sunfish/pins_init.lean`. In-repo survey 75/91 MATCH
(82.4%), 0 DIVERGE.

**THE MESSAGE STEP, AND TWO MORE INSTRUMENT BUGS (2026-08-13).** The
class comparison below was one resolution step; the MESSAGE is the next.
The runner now emits `ClassName: message` (`errMessage`, Main.lean) and
carries it in the batch JSON as `exnmsg`; `harness/script_corpus.py`
compares the whole line whenever the model carries a message, and
`harness/leanpy_survey.py` reports SAME/DRIFT/ABSENT as telemetry rather
than a verdict. It found three things immediately:

* **`script_corpus.py` oracled against `sys.executable`** — CPython
  **3.14** on this machine — while the model's tier is specified against
  3.9 and `leanpy_survey.py` has always pinned it. Every "MATCH" the
  pinned regression corpus reported was measured against the wrong
  reference. Visible only because 3.13+ appends `Did you mean: …?` to a
  `NameError`. FIXED: `default_oracle()` pins `python3.9`, and the oracle
  version is printed with every run.
* **`diff_test.py` had the same bug, in-process** — it imports each `.py`
  by path and calls the function, so its oracle is the interpreter that
  launched it. All 998 cases, the harness that gates every commit. FIXED
  by re-execing into the pin (`LEANPY_CPYTHON` overrides,
  `LEANPY_NO_REEXEC` disables), with a LOUD warning if the pin is not
  installed, and the version printed in the summary.
* **The model's payload-free `PyErr` constructors conflate distinct
  CPython messages** (recorded, open): `ZeroDivisionError` is "integer
  division or modulo by zero" from `//`/`%` but "0.0 cannot be raised to
  a negative power" from `0 ** -1`; `IndexError` is list/string/tuple
  "index out of range"; `KeyError` prints the missing key's `repr` (now
  renderable — `reprVal` exists); `AttributeError` names the type and the
  attribute. Giving them payloads is the next step; until then the survey
  reports them as ABSENT and NOTHING is invented. `StopIteration` was
  exact already (CPython raises it bare) and now says so.

**THE CLASS TIER IS NOT THE STDLIB FRONTIER — the ranking was an
ordered-check artifact (2026-08-13, MEASURED).** The dynamic telemetry
names the FIRST admission that stopped a file, and `runScript`'s
admissions are ordered, so a wall that always sits behind another one
reads as the frontier when it is not. `classesCreationPure` is checked
before execution ever reaches an import statement, which is why "108
files: class CREATION effects" topped the ladder for a week.

Re-measured with a per-file WALL SET instead of a first-blocker count:

* stdlib sweep, 162 refusing files — `import` is **present in 155** and
  **sole blocker in 7**; `class-creation` is present in 105 and **sole
  blocker in ZERO**. Of the 112 files that refuse on class creation, 111
  also contain an import; the one exception is `graphlib.py`.
* the vendored `Lib/test` corpus is the same story: all 8 files import
  (`test_builtin.py` 33 times).
* in-repo, `class-creation` is sole blocker for 2 files (`cls_lab.py`,
  `cls_effect_script.py`).

So an inheritance/class-body tier — worth building as a LANGUAGE SURFACE,
and still the biggest single hole in the class model — would move the
stdlib sweep by ONE file. The frontier for whole-program completeness is
`import`, which is currently out of scope BY KIND, and behind it a broad
tail (Assert present in 47, Delete 74, With 69, Starred 68,
`Constant:bytes` 51, JoinedStr 46, BitAnd 43, Set 27, Lambda 26, Global
23, DictComp 18) — no single one of which is sole blocker for more than
one file either. Closing `import` alone unblocks 7; whole-program stdlib
completeness needs `import` PLUS most of that tail.

THE INSTRUMENT THAT SAYS SO is now part of the survey: `census` returns a
WALL SET per file and the report ranks by `sole` (files where the wall is
the ONLY one) alongside `present` (the number the ordered ranking
flatters). Ranking tiers by `present` is what produced the wrong
priority; `sole` is the number a tier would actually buy. Note the
recorded caveat: the wall set is STATIC and only covers walls it knows,
so files refusing for a dynamic reason land in
`(none detected statically)`.

RECORDED CONSEQUENCE FOR THE LADDER: `import` deserves its scope decision
revisited rather than restated. THE ONE PIPELINE makes a Python-only
module system conceivable for the first time — importing a pure-Python
module is running its top level in its own namespace, which is now
exactly what `runScript` does — though most stdlib imports reach C
modules (`sys`, `_collections_abc`) that no such system can execute, so
the honest ceiling needs measuring before the work is committed to.

**THE LAST SEAM CLOSED (2026-08-13)** — docs/memory-model.md §the one
pipeline. The general `for` and `try` got control shells mirroring
`execStmt` arm for arm (value sequences, the live heap-list index cursor,
the lazy generator cursor, the retained-state `try` covenant, every
refusal verbatim), so their body bindings publish per statement and a
function called from inside a top-level loop reads what the loop wrote.
`while … else` is the only compound still delegated wholesale;
`scriptFlushCoherent` stays as the guard that would catch the next
missing shell. The refusal left both sweeps.

THE INSTRUMENT GOT SHARPER WITH IT: both harnesses compared stdout + exit
code only, and CPython maps EVERY uncaught exception to exit 1 — so two
different exceptions looked identical. `harness/leanpy_survey.py` and
`harness/script_corpus.py` now also compare the exception CLASS, read off
the last traceback line. It caught its first false agreement immediately:
sunfish.py exiting 1 with the model's `NameError` against CPython's
`ModuleNotFoundError` would have been counted a MATCH.

The stdlib sweep is deliberately NOT in the default corpus file: running
arbitrary stdlib top level under the oracle has side effects (a browser,
a window, a server), so it stays an explicitly invoked measurement with a
`--exclude` safety list, not something a routine harness run triggers.

### CPython's own test suite as the official bench (owner-directed, 2026-08-07)

Adopt CPython's `Lib/test` as `leanpy`'s official correctness bench: there
is no independent Python conformance suite — `Lib/test` IS the standard
every alternative implementation (PyPy, RustPython, GraalPy) tests
against, and RustPython's vendored-copy + expected-failure-manifest model
is the closest precedent to our situation. Staged:

1. **NOW (cheap):** vendor the CPython **3.9-branch** `Lib/test`
   (matching the pinned reference version) — in-repo snapshot or
   submodule, exact commit recorded. Mine it: extract small
   self-contained assert sequences from `test_grammar`/`test_bool`/
   `test_compare`/`test_dict`/`test_list`/`test_builtin` into leanpy
   corpus scripts, each provenance-tagged
   (`# from: Lib/test/test_dict.py:TestDict.test_getitem`) — official
   test CONTENT without the unittest harness. A handful of dict/list
   extractions is a natural H2 deliverable. H3 note (2026-08-08): no
   suitable small CLASS extraction exists in the vendored set —
   CPython's class-flavored tests (`test_grammar.test_classdef`,
   `test_compare`) are dunder/inheritance-protocol tests, exactly the
   loud frontier; the class corpus script is hand-written
   (`harness/scripts/class_script.py`) until `Lib/test/test_class.py`
   territory enters the tier.
2. **LATER:** a micro-extraction tool pulling assert-shaped statements
   from test methods at scale.
3. **H3+ MILESTONE:** run actual test files under `leanpy` with a
   RustPython-style expected-failure manifest; "% of CPython's own test
   files passing unmodified" becomes the headline completeness metric and
   the manifest becomes the feature-ladder priority queue.

Caveat (recorded): CPython tests probe implementation details beyond the
language (GC timing, `sys` internals, exact messages) — PyPy's copy is
modified for the same reason; our loudness invariant plus a documented-
deviations list is the mechanism for the same problem.

## A C surface (long-horizon direction; owner-scoped 2026-08-07)

A structured-C subset tier (Clight-like: no `setjmp`, restricted control
flow, UB loudly refused — the loudness invariant ports directly) as the
project's SECOND language surface, reusing the whole architecture: extract
via a C frontend → deep embed → definitional interpreter → differential
harness with gcc as reference → VC walker. Sequenced after the Python
ladder matures (post-H3/H4). No action during H2.

Scope decisions (recorded from the owner discussion):

* **No sunfish deliverable attached.** The sunfish formal program's scope
  is CLASSIC sunfish only; `csunfish.c` is the NNUE C engine and we are
  not proving the NNUE engines. The C tier stays a generic lean-surfaces
  growth direction unless a classic C sunfish ever exists (none is
  planned). Nuance kept on record: the search theorems are
  eval-parametric (eval enters only via `Bounded`-style side conditions),
  so a C NNUE engine's search skeleton COULD inherit the same specs
  without proving anything about the network — an open option
  deliberately not exercised, not a wall.
* **DECLINED: executing CPython's C-implemented builtins under the C
  tier.** CPython C modules are entangled with the PyObject runtime
  (refcounting, type objects, error protocol) — faithfully running them
  means modeling CPython's own runtime, a larger object than the Python
  language itself. Every serious alternative implementation
  (PyPy/RustPython/GraalPy) natively reimplements builtins instead;
  `leanpy` does the same (Lean-native builtins + differential
  validation).

## Python tier: the sunfish ladder (steps 3-6)

Steps 1-2 are BUILT (G1 constant globals; `for` over lists/tuples;
builtins `max`/`min`/`abs`/`int`) with proved sunfish acceptance examples
(`Examples/python/sf_consts`, `sf_builtins`, `sf_bound_for`,
`sf_bound_tree`). The remaining steps toward running Lean proofs against
sunfish.py as shipped, in dependency order, each with its blocking design
decision:

3. **Dicts — BUILT (H1-proper, 2026-08-07),** via option (b): the heap
   layer of docs/memory-model.md. Literals, read/write (aliasing-visible,
   `KeyError` faithful), `len`, `in`, `.get`, `==` (`heapEq` with cycle
   detection), truthiness, dynamic `is`; G1 module init allocates
   top-level dicts into `initWorld` (`piece`/`pst` and the REAL
   `MATE_LOWER`/`MATE_UPPER` defining expressions — proved in
   `Examples/python/sf_pst`; the module-global TT shape — with the first
   stateful `CallsIn` proofs — in `Examples/python/sf_tt`). Still out,
   loudly: live dict iteration (`for k in d` — no snapshot shortcut),
   `.keys/.values/.items/.update/.pop`, `del`, comprehensions, the pst
   padding loop's constructs (`.items()`, lambdas, `sum` over a
   generator).
3b. **Lists (H2) — the IN-WORLD half is BUILT (2026-08-07),** per
   docs/memory-model.md §list semantics: heap `Obj.list` for every
   interpreter-built list (literals, G1 tables, `sorted` results), the
   full read/write/method/membership/equality inventory, the live
   `for` cursor (`execForList`), snapshot freeze for returned lists
   (`freezeB`/`freezeH`), and the `CallsIn` aliasing exemplars
   (`sf_hist`, `list_lab`). REMAINING (the recorded next step): the
   BOUNDARY FLIP — wire `RVal.thawArgsH` into `callFunction` so
   `Val.list` arguments become heap objects (machinery built:
   `thawH`/`listFree` bridges, `eq_thaw_of_freezeH`); it carries the
   list-example proof rebase (`sf_bound_for`, `sf_bound_tree`,
   `sf_bound_rec`, `bench_bisect`, `bench_statistics`) — the rescue
   route's ENGINE is now BUILT (2026-08-08):
   `execForList_eq_execFor_snapshot` (Obs.lean) proves the live cursor
   IS `execFor` over the object's snapshot for heap-free bodies in
   heap-free modules (worlds pinned by `worldInv`, induction on fuel),
   so the frozen-tail `for` induction pattern survives the flip by one
   rewrite per loop. Remaining: wire `thawArgsH` into `callFunction`,
   rebase the five example proofs through the lemma, then the
   arg-mutation harness rows go live and `+= `/list concat can revisit
   the heap-free-fragment question.

4. **Classes — BUILT (H3, 2026-08-08),** per docs/memory-model.md
   §class semantics: ClassDef end to end (the three sunfish ClassDef
   bodies represented), methods flattened to qualified-name functions
   through `callIn`/`CallsIn` (no new call judgment), `Obj.instance`
   with mutable self, faithful `AttributeError`, the dunder guard making
   default-object semantics sound, `Searcher`'s tables proved
   (`Examples/python/sf_searcher`: the cross-call write/read pair).
   **namedtuple — BUILT (2026-08-08),** per the recorded VALUE-like
   decision (memory-model §class semantics): `RVal.ntuple` immediate
   values, ingestion-time recognition of `X = namedtuple(…)` under the
   benign import (all-or-nothing binding census; the extractor-recorded
   `has_global` makes the `global`-leak check exact), constructor calls,
   field reads as tuple indexing, tuple-erased equality/hashing — the
   `tp_score` key pattern proved symbolically
   (`Examples/python/sf_position`; the real sunfish.py's `Move`/`Entry`
   recognize as-is), loud boundary for namedtuple results.
   H5 slice 1 (2026-08-08): the value-like SUBCLASS shape is
   recognized (`ClassDefn.ntBase`, same census) and INSTANTIATION
   builds the immediate value through the subclass — the real
   sunfish.py's `Position` now constructs (`ok = true`).
   H5 slice 2 (2026-08-08): METHOD CALLS on the immutable self are
   LIVE (`ntupleCallPlan` dispatch, `self` = the VALUE through `callIn`;
   identity via the census tname-clash refusal;
   `Examples/python/sf_position`: `position_mirror_callsIn` — the first
   subclass-method theorem, symbolic in the score). This step is DONE.
5. **String methods + slicing — BUILT (H5 strings, 2026-08-09),** per
   docs/memory-model.md §string semantics: structured `Slice` end to
   end (absent bounds = `Constant None`, CPython's own compilation;
   step-first validation order), CPython-exact str slices both
   directions, `.swapcase()`/`.isupper()` (ASCII-exact, non-ASCII
   loud), `.index()` (code-point-exact), the pure `strCallPlan`
   dispatch, meta-proof arms (heapFree/fuelMono/worldInv/name
   walkers), the `str_lab` differential battery and `str_script`
   corpus. **THE MILESTONE LANDED WITH IT** (`Examples/python/sunfish`
   — sunfish.py byte-identical): `rotate_callsIn` /
   `rotate_null_callsIn` / `rotate_home_callsIn` — `Position.rotate`
   score-negation on the shipped file, symbolic in the score AND the
   world. Remaining, recorded: membership on strs (`q in " \nPNBRQK"`
   — gen_moves), `for` over a str / `enumerate`, str unpacking,
   `ord`/`chr` (parse/render), `sorted()` on strs; and the
   attribute-call heapFree whitelist is still `.get`-only — extending
   it to the pure str trio is sound (dict/list referents refuse those
   names; a heap-free module has no classes) but needs the
   `attrCallPlan_get_heapFree`-family lemmas generalized and the
   `worldInv` attribute case reworked from its `attr = "get"` subst.
   `Position.value()` on the shipped file now gates on `ord`-free
   pieces only (pst dict reads are in tier — symbolic dict-read walker
   support is the proof-side gap); `gen_moves`/`bound()` gate on
   step 6.
6. **Generators (hardest) + `sorted(key=)`.** `moves()` interleaves
   search effects with iteration and `bound` consumes it lazily —
   the beta cutoff means eager pre-expansion diverges on real trees.
   DESIGN DECISION (owner): semantics as (a) CPS/step-indexed iterator
   values in `Val`, (b) a desugaring for the restricted
   generator-consumed-by-one-for-loop shape sunfish uses, or (c) keep
   generators out and certify a generator-free `sunfish_core.py` that
   sunfish imports (the transliteration then ships as the engine).

   H4 DESIGN NOTES (2026-08-08, design only — elaborating memory-model
   §staging's defunctionalized-continuation decision; nothing here
   pre-empts the (a)/(b)/(c) owner decision, and the extractor items are
   shared by all three routes):

   * **Representation.** `Obj.iterator` carries the suspended frame as
     DATA: the generator's qualified function name, its locals env, a
     status (created/running/suspended/closed — `running` makes
     re-entrant `next` the faithful `ValueError`), and the continuation
     as a STRUCTURAL PATH into the body — v0 tier admits `yield e` only
     in STATEMENT position inside `for`/`while`/`if` nests (exactly
     sunfish's `gen_moves`/`moves` shape), so the path is a list of
     statement indices + enclosing loop cursor states, never an
     arbitrary expression context; `yield` in expression position
     (consumed `send` values) stays loudly out.
   * **Stepping.** A new FROZEN mutual-block member
     `stepIter m fuel w a : Run World (Option RVal)` — `some v` = next
     yield, `none` = exhaustion (status → closed). `for x in gen`
     consumes through the live-iterator arm of the `for` dispatch;
     `break` leaves the iterator SUSPENDED (CPython semantics — the beta
     cutoff depends on it). Resumption re-enters the body via a
     path-driven executor (`execStmtsFrom`), a mutual-block addition
     following the recorded conjunct-appended-LAST discipline for
     `fuelMono`/`worldInv`.
   * **heapFree.** Generator creation ALLOCATES and syntax cannot tell a
     generator call from a function call — `Module.heapFree` must also
     require "no generator defs", mirroring the H3 `classes = #[]`
     carve-out; generator-using modules live on `CallsIn`.
   * **Extractor.** A def containing `yield` (own scope only — unlike
     `has_global`, nested defs are their own generators) is a generator
     regardless of reachability (CPython rule): envelope flag
     `is_generator`, plus structuring today's `Unsupported "Yield"` into
     a statement-position node for the tier above.
   * **Acceptance.** Staged: a lab generator (counter/interleaved-effect
     shapes) with differential rows pinning suspension-across-`break`
     and mutation-between-`next`s; then sunfish's `moves()` consumed
     lazily by `bound`. `sorted(key=)` is orthogonal (paired here only
     because sunfish's move ordering needs both).
   * **gen_moves THEOREM STATEMENT — decided (owner, 2026-08-09).** Of
     the three drafted statement shapes — (1) rule-predicate
     set-equality, (2) equality against a reference enumeration,
     (3) a property bundle — Thomas picked **(2), reference-enumeration
     equality with ORDER pinned** (`bound`'s cutoffs depend on move
     order, so order stays part of the claim). His design note,
     recorded: "we can make the reference implementation very simple,
     because it doesn't need to be fast" — the Lean reference must
     optimize for OBVIOUSNESS over efficiency: the most
     naively-readable enumeration of sunfish's pseudo-legal moves
     (plain nested scans, no cleverness), because its whole job is to
     be trustworthy by inspection. A semantic layer on top (the rule
     predicate or a bundle) stays open for later and must meet the
     same simplicity bar. Nothing starts before this generator tier
     lands.

## H4 generators — BUILT (2026-08-09)

Step 6's route is taken and the generator-FUNCTION tier is live
(docs/memory-model.md §generator semantics). Of the recorded (a)/(b)/(c)
owner options this is (a) done properly: step-indexed iterator objects
with a defunctionalized continuation. (b) was never viable —
`gen_moves` has ~six yield sites at different control-flow depths, so
plain desugaring collapses into the same state machine anyway — and (c)
is ruled out by laziness being semantically load-bearing: an unconsumed
yield must not run its TT-writing search, and consumers break early.

**Owner-level note, surfaced not decided.** The stage brief said
"generators as IMMEDIATE VALUES (no heap)". That is not sound, and the
recorded design (commit 7d23f17, memory-model §staging) already said
heap: a generator is IDENTITY. `gen_lab.aliased` binds one generator to
two names and steps through each — CPython advances the single shared
frame and answers `1`; an immediate value restarts and answers `0`.
`gen_lab.two_phase` is the same point for `break`. Both are CPython-
checked differential rows, so the choice is settled empirically, not by
taste. The rest of the brief — defunctionalized STRUCTURAL-PATH
continuations, statement-position yields, `for`-consumption, `break`
abandonment, loud refusal for send/throw/yield-from/finalization — is
implemented exactly as written.

**BUILT since (2026-08-09, second pass):** generator EXPRESSIONS are
LOWERED at ingestion (`lowerGenExps`, Json.lean) per CPython's own
compilation, with the by-value CAPTURE rule below; and `enumerate` /
`itertools.count` are lazy iterator objects sharing the generator
stepper (`enumSeq`/`enumList`/`countFrom` frames). Four genexps lower on
the shipped file.

**THE BLOCKER for the named target, found by running `gen_moves` on the
shipped file — and it is not generators.** `Position.gen_moves` executes
correctly right up to `directions[p]`, then refuses: EVERY module-level
global of sunfish.py is POISONED. `globalsStep` carries one boolean,
`complete`, and sets it false at the first top-level statement it cannot
analyse — which is `import time`, the very first — after which every
later binding is poisoned, `directions`/`A1`/`H1`/`A8`/`H8`/`N`/`E`/`S`/
`W` included. The blunt rule is sound but far too coarse; its own
docstring gives the precise reason ("their RHS could read state an
unprocessed statement changed"), and that reason is a DEPENDENCY, not a
position.

The designed fix — an owner-visible change, because it moves the
NameError/loud frontier: replace the single `complete` flag with a
DIRTY-NAME set. An out-of-tier top-level statement contributes to it
(a) the names it binds (`stmtBinds`) and (b) the primary of every
subscript/attribute store inside it (`pst[k] = …` dirties `pst`); an
UNANALYSABLE statement dirties everything, exactly today's behaviour. A
later binding then evaluates normally unless its RHS reads a dirty name.
On sunfish that resolves precisely the right set: the three imports
dirty only `time`/`count`/`namedtuple`; the `for k, table in pst.items()`
loop dirties `k`/`table`/`pst`, so `K_MID = pst["K"]` stays poisoned
(correct — `pst` really is mutated) while `A1, H1, A8, H8 = …`,
`N, E, S, W = …` and `directions = {…}` all resolve. `MATE_LOWER` reads
`piece`, which nothing dirties, so it resolves too. Two judgment calls
to confirm before building it: whether a simple import may be treated as
benign at all (a circular import could in principle mutate this module —
the namedtuple census already assumes this for one exact import), and
whether `complete` should then stay TRUE, which would turn today's loud
refusal for an unknown module-level name into a faithful `NameError`.

**Open, in order:**

1. **Generator EXPRESSIONS.** ~~Structured end to end (`Expr.genExp`,
   extractor `GeneratorExp`, the single-clause non-`async` shape — every
   genexp in the real sunfish.py fits it) but NOT lowered: evaluating
   one refuses loudly. The lowering is decided and should ride the same
   machinery, per CPython: `parseModule` replaces each genexp with a
   call `<genexpr@n>(<iter>, <captures…>)` and synthesizes the generator
   function `for <target> in .0: if <ifs>: yield <elt>`, first parameter
   `.0` (CPython's own name — no Python identifier collides). The one
   real design point is CAPTURE: CPython closes over free names BY
   REFERENCE, the lowering passes them BY VALUE, and the two differ iff
   a captured name is rebound between creation and consumption. v0 rule:
   admit a free name only if it is a PARAMETER of the enclosing function
   (never rebound) or a module global (resolved dynamically anyway) —
   anything else refuses loudly. That admits `king_capture`'s genexp
   (free: `self`) and refuses `bound`'s (free: `val_lower`, a local);
   relaxing it wants a rebinding analysis, recorded here rather than
   guessed.~~ **DONE** — implemented exactly as designed; the rule
   admits `king_capture`'s genexp and refuses `bound`'s, as predicted.
2. ~~**The G1 dirty-name pass** above — the actual blocker for the named
   target. Nothing else on this list gates `gen_moves`.~~ **DONE**
   (2026-08-09) — built as designed, with both owner calls answered as
   recorded below; `Position.gen_moves` now runs on the shipped file and
   yields CPython's 20 opening moves in CPython's order.
3. **`sorted(key=)`** — orthogonal but needed for `moves()`'s ordering,
   as is `sorted`/`max`/`all` over a generator (all three DRAIN it, so
   they need the stateful stepper, not the pure helpers they use today).
   Note `sorted(…, reverse=True)` is a KEYWORD call, which the extractor
   already flags `call_unsupported` — so `bound`'s consumer needs
   keyword arguments too, not just the draining forms.
4. **`moves()` is a NESTED def — the capstone needs closures too.**
   Found while running the H4 census on the shipped file: sunfish's
   lazily-consumed `moves()` is not a module-level generator at all, it
   is a `def` INSIDE `Searcher.bound`, closing over
   `pos`/`gamma`/`depth`/`root`/`self`/`val_lower`/`killer`. It ingests
   as `Stmt.unsupported "FunctionDef"` (v0 has no nested defs and no
   closures), so "moves() consumed lazily by bound" needs a nested-def
   tier ON TOP of the generator tier — an owner-level scoping fact that
   the H4 staging note did not anticipate. `Searcher.search` IS a
   method-level generator and is in reach today; `Position.gen_moves`
   likewise. The census guard in `Examples/python/sunfish/spec.lean`
   pins all of it.
5. **`gen_moves` itself.** Its remaining tier gaps are closed (H5
   iteration: `q in " \nPNBRQK"`, `for` over a str, membership on the
   value tuples in `directions[p]`), EXCEPT `enumerate(self.board)` and
   `count(i + d, d)` from itertools — both are ITERATOR objects and now
   have a home: another `Obj.generator`-shaped builtin (or a builtin
   frame kind), lazy by construction, with `count` infinite. ~~That is
   the last interpreter surface before the theorem.~~ **DONE** — both
   are generator frames now; `gen_moves` runs to `directions[p]` and
   stops only on the G1 blocker above.
6. Then the recorded gen_moves THEOREM (statement decided at f536d93 —
   reference-enumeration equality, order pinned, the reference written
   for obviousness).

Smaller, found on the way: leanpy's live-suffix shell has a `while` case
only, so a `print` inside a top-level `for` (or a `for` over a
generator) is loud — `harness/scripts/iter_script.py` and
`gen_script.py` work around it; extending the shell is cheap. And the
whole interpreter mutual block now carries explicit
`termination_by structural fuel`: adding the generator members made
structural inference silently fall back to well-founded recursion, which
broke every kernel `rfl` — the mergeSort trap, caught by `Tests.lean`
rather than by anything that names it.

## Session stop point (2026-08-09, after the genexp/iterator pass)

Stopped CLEAN at master `a56b446`; the triad was green at that commit
(`lake build` 3641; docs_check 67/67; diff_test 615 rows 0 failed, 30
whitelisted; corpus 17 scripts 0 failed) and this section is the only
change after it. Four commits this session: `d8710b1` (H5 iteration),
`14a4b2c` (H4 generator functions), `ab75551` (stop point), `a56b446`
(genexp lowering + `enumerate`/`count`).

**The next step is ONE thing: the G1 dirty-name pass** (designed in the
H4 section above). It is the only blocker between here and the named
target — `Position.gen_moves` already executes on the shipped file and
stops exactly at `directions[p]`, on module-init poisoning rather than
on anything generator-shaped. Two judgment calls need an owner before it
is built, both recorded there: whether a simple import may count as
benign, and whether `complete` should then stay TRUE (which converts
today's loud refusal for an unknown module-level name into a faithful
`NameError`).

After it, in order: the gen_moves theorem (statement decided at
f536d93 — reference-enumeration equality, order pinned, the reference
written for obviousness; a first draft of the reference and the two
encoding judgment calls it forces are in the session report), then the
draining consumers (`sorted`/`max`/`all` over a generator, plus keyword
arguments, which `sorted(…, reverse=True)` needs), then the nested-def /
closure tier that `bound`'s `moves()` requires.

Housekeeping unchanged: this clone lives in a /private/tmp scratchpad
that macOS purges, local master is ~60 commits AHEAD of `origin/master`,
and the bundle in `~/repos/lean-surfaces-backup/` is refreshed through
`a56b446`. PUSHING (or relocating the clone) is still an open owner
decision.

Cross-cutting, carried forward: `py_vcgen` cannot walk `for` loops; the
two while-loop walker gaps in
`Examples/python/sf_bound_loop/proof.lean.blocked-by-py_vcgen-gaps`;
`arrVal_getElem`-family lemmas still example-local (F-6); leanpy v0
cannot run a module containing an import at all, and its live-suffix
shell has a `while` case only (so a `print` inside a top-level `for` is
loud); and the `Position.value()` warm-up on the shipped file is still
unclaimed — note it now needs the same G1 fix, since `pst` is poisoned.

## The G1 dirty-name pass — BUILT (2026-08-09)

The blocker recorded above is gone. `globalsStep`'s single `complete`
boolean is replaced by TWO independent facts (docs/memory-model.md
§the dirty-name pass is normative):

* **poisoned, per NAME** — an out-of-tier top-level statement poisons the
  names it BINDS anywhere in its subtree (`Stmt.g1Binds`) plus the
  primaries it STORES into (`Stmt.g1Stores`). Poisoning needed no new
  state: it is an ordinary rebinding to `none` in the accumulator. That
  exposed a latent bug worth naming — `resolvedG` dropped the `none`
  markers, so the poisoning entry (which sits in FRONT of the value it
  invalidates) would have RESURFACED the stale value; it now keeps only
  the latest binding per name (`resolvedGAux`), agreeing with `lookupG`.
* **analysable, per MODULE** — cleared only when a statement's binding
  set could not be determined, which also poisons the whole accumulator.
  This is the sole gate on the faithful `NameError`.

**The two owner calls, as answered.** (1) A simple import counts as
benign only through an EXACT-TEXT whitelist, `benignImportBinds`
(Ast.lean) — the table the namedtuple census already had for its single
member, now shared by both and extended to the three stdlib imports the
shipped file uses. Each row records whether the model already gives the
bound name a meaning: `count` IS `itertools.count` in `isBuiltinName`,
so G1 binds nothing and resolution falls through; `time` is unmodelled
and is bound POISONED (loud — never a fake `NameError` for a name
CPython did bind). (2) `analysable` is a SEPARATE per-module flag, so
the `NameError` is never invented for a file we did not fully
understand. One thing the design did not anticipate: making sunfish
analysable would have turned `__name__` into a fake `NameError`, since
the import machinery binds it and no statement does — `isModuleDunder`
now keeps `__name__`/`__doc__`/… loud in every module.

**Result on the shipped file** (pinned by `#guard` in
`Examples/python/sunfish/spec.lean`, not merely described): `time`
poisoned; `piece`/`pst` valued, then the `for k, table in pst.items()`
loop poisoning `pst`/`padrow`/`table`/`k`, so `K_MID = pst["K"]` stays
correctly poisoned; `A1/H1/A8/H8`, `initial`, `N/E/S/W`, `directions`,
`MATE_LOWER`/`MATE_UPPER` and the search constants all resolve; the
module is analysable. `Position.gen_moves` then RUNS: 20 moves on the
real opening board, CPython's answer in CPython's order.

Validation beyond the pinned run: the model's `gen_moves` on the shipped
file was checked against CPython on 53 positions / ~1195 moves — 40
reached by random play from the opening plus 13 adversarial boards
(promotion push and promotion captures, en passant, king-passant
squares, castling in all four rights combinations, sliders, edge
knights, and both pawn double-move boundaries). All agree, order
included.

**OPEN, owner-level — the module-init mutation gap.** The poisoning scan
is syntactic, so it does not see a mutation performed by code the
statement CALLS: a top-level `foo()` whose body runs `tbl["k"] = 1`, or
an alias taken inside a callee, mutates a table that stays clean. This
is PRE-EXISTING — the old `complete` flag guarded later BINDINGS, never
mutation — but more names resolve now, so more rides on it, and on
sunfish it is load-bearing: the last top-level statement is
`if __name__ == "__main__": main()`, and the model resolves `directions`
without accounting for it. Two named pieces close it and neither is
built:

1. **G1 is IMPORT semantics** — its own section comment says so ("CPython
   executes a module's top-level statements once, at import time"). Under
   import, `__name__` is the module name, so an `if __name__ ==
   "__main__":` guard with an empty `orelse` is statically DEAD and need
   not be analysed at all. This is exact, not an approximation, but it
   changes what the model claims about a file run as a script, so it is
   the owner's call.
2. **A purity whitelist for the calls that remain.** With `dict`/`sum`/
   `tuple`/`range` and namedtuple construction certified store-free, ANY
   other call in an out-of-tier top-level statement could soundly poison
   every ref-carrying name. On sunfish that leaves the `pst` loop's
   opaque `padrow` lambda poisoning `piece`/`pst` (costing `MATE_LOWER`,
   which `Searcher.bound` will want) and nothing else — `directions`
   survives, because every statement after it is either in tier or a
   whitelisted call.

## Harness batch mode — BUILT (2026-08-10)

The differential battery no longer pays the `lake` startup per row.
`leanmodels-run --batch <jobs.jsonl>` (Main.lean) takes one job per line
(`{"path":…,"function":…,"args":[…],"fuel":N?}`), parses each envelope
once per distinct path, and prints exactly one canonical result line per
job, in order, flushed per line; a job the runner cannot execute emits a
`runner-error` line (the row count stays honest), mirrors to stderr, and
forces a nonzero exit — loud, never absorbed as agreement.
`harness/diff_test.py` now runs ALL rows through one such process and
streams per-row verdicts to stderr. Measured on the full battery: 615
rows in ~11 s wall including the up-front `lake build` replay — the
per-row shape (one `lake exe` per row, each replaying the build graph)
took HOURS on the same rows. Never reintroduce the per-row shape.

Next milestone unchanged (item 3 above, recorded only — not started):
the draining consumers — `sorted(key=)` and `sorted`/`max`/`all` OVER a
generator (they drain it, so they need the stateful stepper), the
`moves()` ordering surface — plus keyword arguments at call sites.

## H6 keyword arguments — BUILT (2026-08-10)

Call-site keywords are live (docs/memory-model.md §call-site keyword
arguments): the extractor STRUCTURES plain named keywords (`**` unpacking
stays `call_unsupported`), `Expr.call` carries `kwargs`, and binding is a
pure call-site merge onto a COMPLETE positional array (`mergeKwArgs`) —
`callIn`'s covenant signature untouched. Coverage: module `def`s by name
and namedtuple-subclass methods (`pos.rotate(nullmove=True)`, the shipped
shape); faithful binding `TypeError`s gated on `argsOk`; loud everywhere
else (heap-receiver methods — note sunfish's `self.bound(…, root=True)`
will want that arm one day, it is closure-gated anyway — class/namedtuple
keyword construction, builtins). `sorted(key=/reverse=)` refuses loudly
until the draining tier lands; `key=` is ADDITIONALLY gated on
first-class callable values (a bound method as a value is loud under H3)
— sunfish's shipped ordering line needs only `reverse=True` over a genexp
of `(value, move)` tuples, NO `key=`. Acceptance:
`Examples/python/kw_lab` (26 differential rows incl. the evaluation-order
exception probes; 3 loud-frontier rows). Fragments: keyword-bearing calls
leave `heapFree` conservatively.

## H6 draining consumers — BUILT (2026-08-10)

The `moves()` ordering surface is live end to end
(docs/memory-model.md §draining consumers, as-built notes there):
`sorted`/`max`/`min` DRAIN generators (`drainIter`, frozen), `any`/`all`
short-circuit and leave the generator SUSPENDED (`anyAllIter`, frozen —
the partial drain is pinned by rows that iterate the remainder);
general-order `sorted` shares ONE relation with `<` (`rvalLt`: tuples
class-erased lexicographic, strs, bool identity preserved), with
`reverse=True` as descending STABLE insertion; the str tier gained
`.islower()`/`.upper()` for the shipped `value()`. The capstone example
`Examples/python/sf_order` runs the shipped ordering line VERBATIM —
`sorted(((pos.value(m), m) for m in pos.gen_moves()), reverse=True)` —
over verbatim `gen_moves`/`value` with the PADDED `pst` (CPython's own
output of the shipped padding loop), whole ordered move lists
differential against CPython, opening board included.

Open, recorded (none started):

1. **`sorted(key=)`** — gates on FIRST-CLASS CALLABLE values (a bound
   method as a value is loud under H3), not on draining. The shipped
   file never uses it.
2. **Instance-receiver method keywords** — DONE (bound() arc pass 1,
   below): the same merge, `.ref` receiver prepended.
3. **`moves()` is a nested def** (the standing capstone gap): closures
   over `pos`/`gamma`/`depth`/`root`/`self`, plus `Searcher.bound`
   itself. The ordering surface now waits ONLY on this.
4. **The module-init padding loop** (`pst.items()` + lambda + `sum`
   over a genexp): would let the SHIPPED file's `value()` resolve `pst`
   instead of the oracle-generated table in `sf_order`.
5. **The ordering theorem** — extend the decided reference-enumeration
   equality from `gen_moves` to the ordered `(value, move)` list
   (`sf_order.order_from` is its concrete anchor).

## H7 nested defs and closures — BUILT (2026-08-10)

The snapshot tier is live (docs/memory-model.md §nested defs and
closures, as-built notes there). The shipped `moves()` ADMITS under the
never-rebound analysis (captures `depth`/`gamma`/`pos`/`root`/`self`/
`val_lower`, generator), and `sf_order.bound_probe` runs the
moves()-shaped nested generator — verbatim ordering line inside, beta
cutoff abandoning it mid-drain — differentially against CPython.

What the FULL `moves()` (and `bound()` around it) still needs, enumerated:

1. **Instance-method keyword arguments** — DONE (bound() arc pass 1,
   below).
2. **`self.tp_move.get(pos)`** — CLAIMED (bound() arc pass 1, below):
   in tier as suspected, no semantics change; `sf_order.killer_probe`
   is the differential row.
3. **`Position.move`** — DONE (bound() arc pass 1, below): `put =
   lambda …` is the H7 nested-def shape; `move` runs as shipped.
4. **`bound()`'s own gates** — sets DONE (bound() arc pass 1, below:
   `set(history)` construction + `pos in self.history` membership, the
   order-blind honest subset). REMAINING AND EXPLICITLY DEFERRED (by
   direction — flagged, not started): `raise Stop` / exception classes
   and the driver's `try`/`except` (needs its own design pass), and
   `time.time()` impurity + the `%` deadline check (needs a RECORDED
   abstraction decision — never a silent stub).
5. **Recursion through a captured `self`** — DONE (bound() arc pass 2,
   below): `-self.bound(...)` from the resumed generator frame is the
   COMPOSITION of built pieces — no interpreter change; battery +
   `sf_order.rec_probe` pin it differentially.

## bound() arc, pass 1 — mechanical blockers (2026-08-10)

The enumerated blockers above, taken mechanically — each construct
designed in docs/memory-model.md, refused loudly outside its tier,
pinned by happy AND refusal battery rows.

**Capstone probes — LANDED** (`Examples/python/sf_order`):
`move_probe` — the VERBATIM `Position.move` (its `put` lambda as the
H7 nested def) + verbatim rotate, the board a search child sees;
`killer_probe` — bound()'s moves() PROLOGUE: `killer =
cache.tp_move.get(pos)` through an instance attribute keyed by the
Position itself (hit / miss-to-None without mutating), the shipped
`if killer and pos.value(killer) >= val_lower:` gate, then the
ordered tail with the beta cutoff. `self.tp_move.get(pos)` is thereby
CLAIMED as in tier (no semantics change was needed). What pass 2
needs is exactly the non-mechanical list: recursion through the
captured `self` (item 5 above), exceptions, `time.time()`.

**Sets — BUILT, the honest subset** (§set semantics): `Obj.pyset`,
heap identity, first-seen order UNOBSERVABLE; `set()`/`set(iterable)`
construction (str/tuple/ntuple/list/set/generator — the generator
DRAINS, `set` leaves `heapFree`) deduplicated by value equality under
the dict-KEY doctrine; membership (probe hashed first — the faithful
unhashable `TypeError`, empty set included), `len`, truthiness
admitted; EVERYTHING order-revealing loud (iteration, `sorted`/`max`/
`min`, mutators, `==`, boundary). `Examples/python/set_lab` is the
checks-only acceptance battery. `sorted(set)` is refused although its
RESULT would be order-independent — deliberately deferred, recorded
here.

**DEFERRED, flagged, deliberately not started** (the non-mechanical
blockers): exceptions (`raise Stop`, the `try`/`except` driver) and
`time.time()` impurity — the former needs a design pass of its own,
the latter a recorded abstraction decision (never a silent stub).

**Instance-method keywords — BUILT** (§call-site keyword arguments,
coverage list): `self.bound(…, root=True)` binds by the same pure
merge with the `.ref` receiver prepended (`attrCallPlan .instMethod` →
`mergeKwArgs`), `argsOk`-gated; builtin heap-receiver methods
(`.get`/`.append`/`.pop`) with keywords stay loud (positional-only in
CPython). `kw_lab.method_kw_instance` (default + keyword override
across two calls mutating self) and `method_kw_instance_err` (the
multiple-values `TypeError`) pin it differentially.

**Lambdas — BUILT** (§nested defs and closures, lambda addendum): a
single-target `name = lambda …: expr` assign directly in a function
body extracts as the H7 `NestedDef` (body = one `Return`; same capture
census — a lambda's locals are its parameters only; same never-rebound
admission, `closure_lab.lam_rebound` the refused exposing row). No new
runtime. `Position.move` runs as shipped; `sf_order.move_probe` is the
verbatim move+rotate differential.

**Recorded regression (pre-existing, found during this pass, NOT
caused by it) — FIXED (2026-08-10, pass 2):** `script_corpus` failed 3
rows — `fib_loop`, `tt_script`, `list_script`, each refusing with
"module-level value of 'X' is outside the G1 tier" where the live
top-level suffix rebinds/mutates a prefix-bound global (`n = n + 2`,
`tt[1] = 11`, `xs`-mutation). BISECTED: 5bb634b passes, 6a79764 (the
G1 dirty-name pass) fails — retroactive per-name poisoning is right
for the closed-function surface and wrong for statements `runScript`
is about to EXECUTE; the whole-module fold poisoned prefix names the
suffix rebinds/stores into. Fix (docs/memory-model.md §dirty-name
pass, Script.lean header): `runScript` folds `initWorld` over the
PREFIX VIEW `mPre` (`topLevel := g1Prefix …`) and threads `mPre`
through the executor; `suffixConsistent` widened (ANY suffix
assignment to a function-read name is loud — the fresh-global case
would otherwise fake a `NameError` under the always-analysable prefix
view); the print arm gained a live-locals shadow probe. Regression
rows: the three scripts back to MATCH plus two refusal rows
(`suffix_rebind_read`, `suffix_fresh_global_read`). Corpus: 19
scripts, 0 failed / 14 matched / 5 loud-blocked.

## bound() arc, pass 2 — recursion through the captured receiver (2026-08-10)

Item 5 of the H7 enumeration, taken design-first
(docs/memory-model.md §nested defs and closures, recursion addendum):
`-self.bound(pos.move(move), 1 - gamma, depth - 1)` yielded from the
resumed `moves()` frame. The recorded claim — the construct is the
COMPOSITION of built pieces (frame-agnostic `evalExpr` dispatch, world
threading through the running frame, per-invocation closure/generator
identity, resume-carried fuel) — held exactly: ZERO interpreter
changes; the pass is design + battery + capstone.

* `cls_lab.method_rec` / `method_mutual` — direct and mutual method
  recursion, one shared `nodes` attribute mutating across the nest.
* `closure_lab.gen_rec` — the bound() shape at lab scale: a nested
  generator yielding `self.tree(n - 1, cut)` through the captured
  self, folded with a cutoff; `(2, 4)` under cut=2 vs `(9, 13)` under
  cut=100 at the same depth — subtrees behind abandoned yields never
  ran.
* `closure_lab.rec_nested_name` — the refusal the admission excludes:
  a nested def calling ITSELF by its own name, refused by the census
  with the predicted reason (no binding before the def); sunfish never
  does this — bound() recurses through the METHOD name on `self`.
* `sf_order.rec_probe` — the CAPSTONE: MiniSearcher.bound with the
  verbatim ordering line inside `moves()`, recursive yields, beta
  cutoff. moves() captures = the shipped set minus `root`
  (`depth`/`gamma`/`pos`/`self`/`val_lower`). Depth-2
  cutting/non-cutting pair `(113, 7)` vs `(113, 15)` — the cutoff
  prunes the recursion TREE, not just the top drain — plus the
  opening board `(46, 2)`; kernel-checked and differential.

Battery: 766 rows, 0 failed, 40 whitelisted. Mechanical note: the
sf_order envelope outgrew the elaborator default —
`set_option maxRecDepth 100000 in load_program` (the sunfish
example's pattern).

REMAINING on the bound() arc after this pass: exceptions now have
their RECORDED DESIGN (docs/memory-model.md §exceptions — DESIGN
ONLY, nothing built: class-identity `PyErr.user`, the exact
`class N(Exception): pass` recognition, single-handler `try`/`except`
on the retained-state covenant, the generator-closing decision with
its pin-current-behavior obligation, and the node-budget deadline
capstone shape). The design surfaced a SCOPING FACT worth repeating:
the in-file driver never sets `deadline`, so `raise Stop` and
`time.time()` are dynamically dead under `deadline = None` — the
shipped deadline-less `bound()` is blocked by the module-init padding
loop (`pst` poisoned), NOT by exceptions. `time.time()` remains
deferred awaiting its own abstraction decision.

## Pass 3 — module-init execution: the padding loop (2026-08-10/11)

The blocker above is GONE. Design first
(docs/memory-model.md §module-init execution, with as-built deltas),
then three landings:

1. **The mechanical value tiers** (function-level too, 828 differential
   rows): tuple/namedtuple slices, tuple repetition, `sum(it[, start])`
   (the fold IS `evalBinOp .add`), `tuple(it)`, and `range` as the
   immediate `RVal.rangeV` — materialize-per-use under a FIXED budget
   (fuel-independent refusals), which makes re-iteration exact.
   `Examples/python/seq_lab` is the battery.
2. **The live pipeline** (`initWorld` = `initFoldLive`): fold step on
   the live state; fold-refused statements EXECUTE through the
   interpreter under per-statement PREFIX VIEWS (sequential name
   resolution — a future-binding read would be silently wrong; the
   faithful import-time `NameError` falls out); the dict-items `for`
   shell with CPython's size check (`RuntimeError` pinned by
   `init_lab`'s hand-built `insLoop`, rollback leaving the table
   poisoned); failed attempts roll back AND poison the live
   accumulator. Resolution consults the live view from the
   statically-POISONED and statically-ABSENT arms only — world-symbolic
   theorems keep their static-first geometry, and pre-pass worlds are
   bit-identical (a `resolvedG` globals cannot contain a marker). The
   static fold gained the DIVERGED discipline (post-divergence bindings
   survive only heap-pure + ref-free; the two heaps may differ);
   `Module.heapFree` gained the `topLevelDefFree` conjunct and every
   closure-call guard its second half. `g1_lab.read_m` FLIPPED from
   refusal to CPython's value (the top-level `while` now executes).
   `Examples/python/init_lab` is the acceptance battery.
3. **The capstone on the shipped file**: the extractor structures
   MODULE-scope single-target lambdas as zero-capture `NestedDef`s
   (CPython symtable: a module lambda has NO freevars — the flagged H7
   admission fork dissolved; its body reads `piece`/`k` through the
   live globals at call time), the padding loop RUNS, the shipped `pst`
   materializes (pinned against CPython's own padded values),
   `K_MID`/`K_END` land, and `Position.value()` — refused since H5
   because `pst` was poisoned — runs on the shipped file with CPython's
   answers.

Deliberately still out (recorded): `.items()` outside the init shell;
top-level `if` bodies still gated by loud `__name__` (the
import-semantics decision stands open); the fold's `.exn` arm still
poisons-and-continues where CPython aborts the import.

## Pass 4 — exceptions, the wall clock, and bound() END TO END (2026-08-11)

Four landings, each triad-green and committed separately:

1. **The stepper's exn obligation discharged** (the §exceptions
   recorded obligation, BEFORE building): `gen_lab.bad*` pin the
   faithful raise differentially, and the raw `#guard` pinned the
   status divergence (stuck `running`) the build then flipped.
2. **Exceptions BUILT** (docs/memory-model.md §exceptions, as-built
   deltas recorded there): `PyErr.user cid name`; the third class kind
   (`exception_base` + the `Exception`-unshadowed census);
   `Stmt.raiseStmt`/`Stmt.tryStmt` (v0 single-handler on the
   retained-state covenant, structured-but-loud everywhere else);
   `stepIter` closes on exn-through-resume (`Run.bindE`/`le_bindE`);
   yield-under-try refused in `genPlan`; `Stop` ADMITTED on the
   shipped census. Battery: `exc_lab` (happy + 15 refusal rows), the
   `try`-driven gen-close differential rows, corpus `exc_script`.
3. **The wall clock decided and recorded** (memory-model §wall-clock
   time): `time.time()` refuses loudly at EVALUATION through the
   poisoned benign-import binding — no stub, sound exactly when
   dynamically dead; `exc_lab.time_dead`/`time_live` are the two
   directions.
4. **THE CAPSTONE — `Searcher().bound()` runs END TO END on the
   shipped file** (memory-model §bound() end-to-end): the last three
   mechanical constructs (attribute `+=`; tuple targets with attribute
   elements — `unpackSeq`/`unpackStoreH`; genexp admission for
   body-assigned names under an immediate drain with provable
   boundness — `LowerCtx.boundBefore`), then 23 differential probes in
   `Examples/python/sunfish/spec.lean`: depths 1–3 from the opening
   board and midgame/tactical/endgame positions, comparing the
   RETURNED BOUND **and `self.nodes`** against CPython — node-count
   equality as the lockstep signal. Labs: `cls_lab` (attr `+=` /
   unpack + refusals), `gen_lab` (drain admission + refusals).

**What full `search()` / UCI-loop coverage still needs** (the honest
next-milestone list, in rough dependency order):

* `self.tp_score.clear()` — dict `.clear()` (a mutator: entries := ∅,
  shape-version bump); the FIRST blocker of `search()`, hit on its
  second line.
* `sum(c.isupper() for c in pos.board)` — str method calls inside a
  drained genexp (`isupper` is in tier; the genexp shape is) — likely
  free already; verify with a row.
* `pst["K"] = K_END if bare else K_MID` — a FUNCTION-BODY store into a
  MODULE-LEVEL dict global (`pst` resolves through the live view; the
  subscript-store arm must accept a live-view `.ref` primary — today
  only locals/static reach it). Also makes `pst` mutation ordering
  visible across search() calls.
* `search()` is a GENERATOR consumed by the driver — stepping it is in
  tier (H4); the MTD loop's `while lower < upper - EVAL_ROUGHNESS` and
  the `yield depth, gamma, score, self.tp_move.get(pos)` are in tier.
  One stepped iteration is the natural next capstone once `.clear()`
  and the `pst["K"]` store land.
* The UCI loop (`main()`) needs `input()`/`print` with f-args,
  `str.split`, list `del hist[1:]` slicing-delete, `dict(zip(…))`,
  `map(int, …)`, float division `/` — driver-side; the leanpy shell is
  the surface for it, far beyond one milestone.
* RECORDED GAP (pre-existing, found in pass 4): `input` is absent from
  `isBuiltinName`, so a hand-driven `main()` run would answer a fake
  `NameError` — add it (loud) with the next builtin sweep.

## Pass 5 — the post-#158 re-pin and the search() arc (2026-08-11, in flight)

The engine repo merged its #158 review: the shipped sunfish.py changed
substantially (142 clean lines; null validation moved INTO moves();
the correction gate widened to `not live`; K_MID/K_END a one-liner;
`pst["K"]` swapped BOTH directions per search; eviction skips
`self.root` via a conditional genexp; chained `pos = self.root =
history[-1]`; deadline inits to `1 << 63` with NO None test —
`time.time()` is dynamically LIVE at every 2048th node). The pinned
example was re-pinned to the new bytes.

1. **Shift/bitwise-or and `yield from` landed FIRST** (the new file's
   census gaps — memory-model §left shift and bitwise or, §yield
   from): `<<`/`|` value tiers (bool-aware `|`; negative `|` operands
   loudly out; `Nat.lor` kernel-reducibility verified before use), and
   statement-position `yield from <genexp>` INLINED at ingestion
   (by-reference exact — the enclosing frame cannot run
   mid-delegation; admission: target occurs nowhere else, `yfNames`).
   Labs: seq_lab (type-pinning bool-vs-int rows), gen_lab (live
   rebound captures, filters, non-genexp + target-leak refusals).

2. **THE RE-PIN** (`Examples/python/sunfish` = post-#158 master,
   byte-identical): census re-pinned (7 lowered genexprs — the
   promotion genexp CONSUMED by the yield-from inlining, the eviction
   genexp dead inside an extraction-unsupported `del`; `moves()`
   captures lost `val_lower`; `__version__` gone; the K_MID/K_END
   tuple-target census rows), the shipped `pst`/`K_MID`/`K_END`
   materialize through the live pipeline (K_END's #158 formula covers
   all 120 squares — corner 59870 pinned), `Position.value` unchanged
   (46/42/5), `gen_moves` pinned on opening + PROMOTION (the inlined
   yield-from on the shipped file) + CASTLING (the two-tuple `for`)
   boards, the Ref enumeration re-mirrored to the new lines (same
   break sets, thirteen CPython pins unchanged), and the bound()
   battery re-derived from CPython (23 pairs, seven changed with the
   rewrite; max 587 nodes). The wall clock is dynamically LIVE at
   every 2048th node post-#158 (memory-model §wall-clock time as-built
   delta): the frontier is pinned by a `nodes = 2047` searcher — one
   node to the loud refusal, not 2048 per build.

3. **search()'s first blockers** (memory-model §search()'s first
   blockers): dict `.clear()` BUILT (`AttrPlan.dictClear` — entries
   emptied, shape version bumped, `None` returned, faithful arity
   TypeError; kwargs loud; dict_lab battery incl. the alias row);
   CHAINED assignment built as the INGESTION SPLIT `splitChains`
   (first-target-name admission, `t1 = t2 = v` ⇢ `t1 = v; t2 = t1` —
   zero interpreter changes; cls_lab: the shipped shape, the
   receiver-reads-NEW-x AttributeError order pin, and
   `chain_attr_first` the refusal); the live-view `pst["K"]` store was
   ALREADY CLOSED by pass 3's live-view consult (init_lab `swap_a`
   claims it).

4. **THE PASS-5 CAPSTONE — `search()` STEPPED on the shipped file**:
   `Searcher().search([posH])` created (H4: no code runs), then FOUR
   steps pinned — the FULL depth-1 MTD-bi bracket to convergence
   (gammas 0 / 34645 / 23, scores 0 / 46 / 37) plus depth 2's first
   yield — every `(depth, gamma, score, move)` tuple AND cumulative
   `self.nodes` (2/4/47/93) CPython-exact; after one step the
   prologue's effects are pinned in the world (`pst["K"]` IS the live
   `K_MID` binding via the queens-on swap; `self.root` IS the root —
   the split chain). The driver surface of the shipped engine now runs
   under the model end to end at depth-1 granularity.

   Cost fact (budget for it): the stepped-search guards raised the
   sunfish spec elaboration from ~900–1800 s to 4782 s (~80 min) —
   the capstone file is now BY FAR the build's long pole; batch
   battery 939 rows / 0 failed / 70 whitelisted; corpus 20 / 0.

**Pass 5 is COMPLETE. The search() frontier after it, surveyed on the
shipped file** (what stepping FURTHER would hit, in order):

* **The 2048-node wall is the ONLY blocker to deeper stepping.**
  search()'s own body is now fully in tier (the post-#158 rewrite
  removed the `isupper` genexp — pass 4's "verify with a row" item is
  MOOT, `isupper` survives only in a comment; the K-swap, the split
  chain, `.clear()`, the MTD frames and the yield tuple all landed).
  Depth-3+ stepping crosses `self.nodes % 2048 == 0` where
  `time.time()` is dynamically LIVE (deadline = `1 << 63`, no None
  test) and refuses loudly — pinned by the `nodes = 2047` searcher
  row. Passing it is the standing OWNER-GATED abstraction decision
  (memory-model §wall-clock time): a recorded deadline abstraction
  (e.g. the poisoned binding admitting a symbolic
  "never-expiring clock" whose reads are pinned dead-by-value), never
  a silent stub.
* **The eviction `del`s** (bound(): `del self.tp_move[next(…)]`,
  `del self.tp_score[next(iter(…))]`) ingest as
  `Stmt.unsupported "Delete"` and are dynamically DEAD below
  TABLE_SIZE — no search-stepping depth reachable under the node wall
  ever executes them. They gate nothing until the wall falls.
* **main()/UCI** stays the leanpy-shell surface (far beyond one
  milestone); `input` is still absent from `isBuiltinName` (recorded
  pass-4 gap — add loud with the next builtin sweep, it rides any
  future Semantics.lean rebuild rather than paying the 80-min pole
  alone).

## Pass 6 — THE TRACE CLOCK (2026-08-11, owner-approved design; in flight)

The 2048-node wall's owner-gated decision is DECIDED: time as an
INPUT, not an effect (docs/memory-model.md §the trace clock is
normative — designed there FIRST, per the standing discipline).
`World` gains a clock trace (`List Int`, opaque integer readings);
evaluating exactly `time.time()` (unshadowed, benign-import census)
pops the next reading; empty trace = LOUD underrun refusal (a spec
error in the input, never a silent 0). The old poisoned-binding
refusal stays for every other impure surface. Record-replay in the
harness: the CPython oracle's monkeypatched clock returns integer
microseconds (`time.time_ns() // 1000`) and records them; the model
replays the same integers — exact equality end to end, no
post-quantization. Trace classes (`WallClock` = unconstrained,
`Monotone` = nondecreasing) land as named predicates; the first
trace-quantified theorem is the pass-5 stepped-search pins FOR ALL
traces (`rfl`: sub-2048-node runs never scrutinize the trace).

Deliberately deferred with it, recorded: a script-mode trace flag
(top-level `time.time()` underruns loudly until then); dyadic-rational
readings (sound — every double is one — but pointless without a float
tier; a future recorded decision); `Monotone`-consuming deadline
theorems ("once expired, always expired") — stated class, nothing
spends it yet.

BUILT (same day) — as designed, with ONE measured correction (memory-
model §the trace clock, as-built): trace-quantified theorems do NOT go
through free-variable `rfl` (elaborator whnf shares no work; 4M
heartbeats died on a ten-iteration run) — the lab theorem
(`clock_lab.pure_sum_all_traces`) lands by SYMBOLIC EXECUTION at small
concrete fuel instead, and the sunfish armed pair + underrun are
concrete kernel pins ([999] continues to CPython's (0, 2049); [1001]
raises Stop at node 2048, world retained). **NEXT MILESTONE, opened by
this measurement — the CLOCK-ERASURE meta-theorem**: for every
interpreter function, a run decided `.ok`/`.exn` from a world with
`clock = []` never consulted the clock, hence runs identically under
EVERY seeded trace (result world's clock = the seeded trace,
unchanged). The fuelMono-shaped mutual induction over the 18-member
block (Obs.lean); its payoff is transporting every existing concrete
empty-trace pin — the whole pass-5 stepped-search battery — to `∀ tr`
statements at zero marginal kernel cost, the honest route to
"safety is trace-independent" at search scale.

## Pass 7 — CLOCK ERASURE lands (2026-08-11)

The meta-theorem above is BUILT (`LeanModels/Python/ClockErase.lean`;
docs/memory-model.md §clock erasure carries the design AND the as-built
record): `clockErase` — the 18-conjunct fuel induction mirroring
`fuelMono` arm for arm — plus the boundary corollaries
(`callFunctionClock_ok`/`_exn`/`_timeout`, `CallsIn.clock_erased`,
`CallsTo.clock_erased`, `initWorld_clock`). Every decided empty-trace
fact in the repo now transports to a `∀ tr` statement at the cost of
one kernel run; `clock_lab.pure_sum_all_traces_transported` is the
exemplar (fuel 4096, `by rfl` + transport — compare the pass-6
symbolic route, fuel 64 and ~20 s of `py_simp`).

**Open, in order (the pass-7 remainder):**

1. ~~**Split the spec pole.**~~ **DONE (same day):** the 927-line
   monolith is now `pins_common.lean` (the ingested program + shared
   probe defs + THE JSON-trap note — after re-extraction edit only
   that file) with per-capstone check files `pins_init` /
   `pins_genmoves` / `pins_bound` / `pins_search`; `spec.lean` keeps
   the census + the rotate theorems (three-file layout unchanged).
   MEASURED per-file elaboration: common 5 s, spec 6 s, genmoves 4 s,
   init 10 s, search 40 s, bound ~14.5 min — the pole is the bound()
   battery alone, and every other re-pin is now seconds. Rode the same
   rebuild: `callFunctionClock_nil` promoted into ClockErase.lean and
   the 18 per-member projections (`evalExpr_clockErased` …) exposed.
1b. ~~**The sunfish `∀ tr` corollaries**~~ **LANDED AS THE TRANSPORT
   (same day), with the honest measured boundary**
   (`Examples/python/sunfish/pins_clock.lean`; memory-model §clock
   erasure as-built): `boundProbeT_all_traces` — any decided
   empty-trace bound probe holds under EVERY seeded trace — compiles
   in seconds; but the `decide +kernel` route for the empty-trace
   HYPOTHESES was tried and is UNAFFORDABLE (one 2-node probe > 16 min
   of kernel reduction, `initWorld`-dominated; core `#guard` is the
   untrusted compiled evaluator, so the batteries were never kernel
   facts). The seeded surface is `#guard`-pinned at empty AND sample
   traces (the batteries' trust level). OPEN: a kernel-affordable
   concrete-run route (kernel-reducibility work on `initWorld`'s hot
   path is the natural candidate) would upgrade the headline rows to
   unconditional `∀ tr` theorems by one application each.
2. ~~**Re-pin to current engine master**~~ **DONE (same day):** the
   pinned file is current master again. The brief's "all in-tier
   constructs" was FALSE by one: the QS filter-before-sort line carries
   a WALRUS in the genexp filter (`if (v:=pos.value(m)) >= val_lower`)
   — ingestion left it un-lowered and `bound()` refused loudly. Closed
   by the §the-walrus-filter tier (memory-model — design first, then
   ingestion-only build: extractor NamedExpr-in-filter structuring +
   `lowerGenExps` walrus locals + the `walrusForbidden` census; ZERO
   interpreter changes, zero new meta-theorem arms). Fresh
   CPython-derived expectations throughout: gen_moves/pst/K tables/
   value()/search-steps/armed-pair IDENTICAL; SIX of the 23 bound()
   pairs changed (the score-cap null gate, the removed band-edge probe
   arm, the killer depth gate); the Ref castling mirror follows the
   two explicit ifs (same moves, same order).
3. ~~Deeper stepping under the trace clock~~ **DONE (same day,
   pins_clock.lean §deeper stepping):** `search()` stepped to TWELVE
   yields — the depth-1/2/3 MTD-bi brackets to convergence and depth
   4's first yield THROUGH the 2048-node wall — under the seeded
   one-reading trace `[0]`; every `(depth, gamma, score, move)` tuple
   and cumulative `self.nodes` CPython-exact (the counting-clock
   oracle: steps 1–11 consume nothing, step 12 consumes exactly one
   reading at node 2048 against `deadline = 1 << 63`). ONE-PASS pin
   discipline: the walker returns rows AND the final world, so trace
   consumption (`[0]` at step 11, empty at step 12) rides the same
   walk — never a from-scratch re-walk per pin (the first draft's four
   walks cost 2917 s; the loud empty-trace direction stays pinned at
   bound() level by pins_bound's nodes-2047 frontier probe).
4. Then, per the standing order: the `.exn` covenant extension for
   `tryStmt` heapFree; the UCI/`main()` surface survey; and the
   kernel-affordable concrete-run route (1b's open item).

## Pass 8 — the module surface completes; the kernel verdict (2026-08-11)

Opened on Thomas's keep-going directive. Milestone 1 (the CAST TIER,
memory-model §the cast tier — design first): `int(<str>)`'s honest
ASCII subset + value-only `str(…)` + the `input`/`str` fake-NameError
fix (both loud builtins now). `parse`/`render` RUN on the shipped file
(CPython-exact, mutually inverse); `hist` confirmed live-view; and
`main()`'s refusal at `import sys, sunfish_ui.uci` is pinned as the
FILE'S OWN boundary: the real UCI loop is an external module shipped
in the wheel, so sunfish.py's in-file surface is now COMPLETE — every
def either runs under the model (rotate, move, value, king_capture,
gen_moves, bound, search-stepped, parse, render) or refuses at a
pinned designed boundary (main's external-module delegation; the
eviction `del`s dead below TABLE_SIZE).

Milestone 1 also closes the KERNEL-AFFORDABILITY item DEFINITIVELY
(memory-model §the cast tier as-built carries the numbers): kernel
reduction is ~1000× native per interpreter step (a 2-node bound() run
> 22 min at fuel 4096; fuel-literal size ruled out); search-scale
`∀ tr` theorems stay transport + native-#guard paired unless the
interpreter is re-engineered for kernel reduction (recorded, not
scheduled).

**Milestone 2 — the UCI surface SURVEYED (same day, the honest
verdict):** `sunfish_ui/uci.py` (551 lines) was extracted and censused.
The blocking construct is not a tier rung — it is CONCURRENCY: the go
loop runs searches on a `concurrent.futures.ThreadPoolExecutor` with a
`threading.Event` for stop/ponderhit, under a `functools.partial`-
rebound `print` and float time budgets. A definitional single-frame
interpreter has NO thread semantics, and inventing them silently is
everything this project refuses. Construct census beyond threads (all
loud today): `import re/random/functools`, f-strings (8), float
division (3), a ListComp, a `with`, a `global`, `input()`/`print`
effects, `%`-format specs. VERDICT, recorded owner-visibly: the model's
"whole-file" claim for sunfish.py honestly TERMINATES at `main()`'s
pinned external-import boundary; running the real UCI interface under
the model is out of scope BY KIND (concurrency), not by distance. If a
UCI-under-model story is ever wanted, the honest routes are (a) a
THREAD-FREE synchronous UCI driver as a new engine-side artifact
(owner-scoped), or (b) leanpy-level line-I/O with every threaded
construct refused loudly — both new named targets, neither started.

**Open after milestone 2:** the tryStmt-heapFree `.exn` covenant
extension (the last recorded proof-layer candidate — a worldInv
exn-clause rework, fuelMono-scale; NO sunfish payoff since class-
bearing modules never enter the fragment); the leanpy script-mode
trace flag (pass-6 deferral — small); deeper stepping beyond depth 4
(more readings, same machinery — cost-gated, not construct-gated).

## The IMPORT CEILING — measured, and the module system is priced out (2026-08-13)

`import` became the frontier the moment the ranking was fixed to `sole`
(above): present in 154 of the 162 refusing stdlib files, sole blocker in
7, with `class-creation` sole blocker in ZERO. And THE ONE PIPELINE made
a Python-only module system conceivable for the first time — importing a
pure-Python module IS running its top level in its own namespace, which
is exactly what `runScript` now does from an empty world.

The recorded next step was to measure the ceiling before committing to
the work. It is measured. **The answer is that the Python-only version
of the idea buys nothing at all**, and the instrument that says so is
`harness/import_closure.py` (`--stdlib --tier --why MODULE`).

### The numbers (CPython 3.9.19, the 167-file stdlib sweep)

* **THE MILESTONE QUESTION, with the survey's own denominator: of the
  154 files that refuse ON `import`, 154 are C-REACHING and 0 are pure.**
  Not one of them. That is the two instruments joined row by row — the
  survey's `REFUSE` verdicts and wall sets against the closure walk — and
  it needed the survey's `--json` to be fixed first, because it had never
  once produced output (below).
* **PURE-PYTHON CLOSURE: 0 of 155.** Same answer from the closure side
  alone, over the slightly wider denominator of every seed with any
  import at all (the extra file imports only from the benign whitelist,
  so leanpy does not count it as a wall). 132 of them reach a C module in
  ONE hop, the other 23 in two. 12 of the 167 import nothing whatever
  (`graphlib`, `this`, `token`, `keyword`, `colorsys`, `copyreg`,
  `__future__`, …) — for those `import` was never the wall.
* The verdict does not depend on how generously the closure is drawn.
  All three scopes agree: IMPORT-TIME (imports in the module body — the
  one with the semantics) 0/155, UNCONDITIONAL (direct children of the
  module body, so certain to execute) 1/147, WHOLE-PROGRAM (function
  bodies included) 0/157. The single UNCONDITIONAL pure file is
  `numbers`, and it is pure only because `abc`'s `from _abc import …`
  sits inside a `try`.
* **THE C SURFACE: 62 distinct C modules.** A seed needs a median of 14
  of them and at most 38; the cheapest need exactly one (`enum` → `sys`,
  `bisect` → `_bisect`, `sre_compile` → `_sre`). Ranked by set COVER —
  a file is freed only when EVERY C module in its closure is native, so
  frequency is the wrong ranking — the price list runs: 8 native
  modules buy 8 files, 12 buy 17, 20 buy 69, 27 buy 90. `sys` alone is
  in 141 of the 155 closures, `_weakref` 128, `_abc` 126, `posix` 88.
* **THE SECOND CEILING: pure-Python is not the same as in-tier.** A
  module system still has to EXECUTE the imported module's top level.
  Of the 208 distinct pure-Python modules appearing in those closures,
  **20 (9.6%)** have no static wall besides `import`. And the compound
  number, computed while GRANTING every C module natively — a
  deliberately generous hypothesis — is that only **19 of 155** seeds
  have a closure whose every pure-Python module is in tier.

### The scepticism the finding itself deserves

"Reaches C" would be a scary word for a solvable problem if the C
modules were things like `itertools` — which IS a C module, and whose
`count` leanpy already models. Stopping at the pure/C split would have
repeated the mistake of ranking tiers by `present`. So the C set is
split by KIND, an argued call written out as `BY_KIND` in the instrument
so it can be disagreed with line by line: a C module that is pure
COMPUTATION is a Lean definition someone can write, while one that IS
the operating system, the IO layer, the thread scheduler or the
interpreter's reflection of itself cannot be modelled without inventing
the thing it reflects.

**8 reach only computational C modules; 147 hit the by-kind
boundary** — `sys` in 141 of them, `_weakref` 128, `builtins` 109,
`_thread` 103, `posix` 88, `_locale` 85. The 8 are individually cheap,
one native module each: `bisect`→`_bisect`, `stat`→`_stat`,
`struct`→`_struct`, `quopri`→`binascii`, `stringprep`→`unicodedata`,
and `sre_compile`/`sre_constants`/`sre_parse`→`_sre`. Three of the eight
want CPython's regex engine and one wants Unicode tables this project
refuses to guess on principle (`str.swapcase` is ASCII-only for exactly
that reason). The genuinely cheap end is three files for three small
native modules.

### What it decides

A Python-only module system is not a smaller version of a module
system; on this corpus it is the empty one. The option only exists
paired with a NATIVE C surface, and that surface is not a tail of
exotica: `sys`, `posix`, `_io`, `_thread`, `marshal`, `_imp` — the OS,
the IO layer, concurrency, and the interpreter's own reflection. That is
the same boundary the UCI survey hit (pass 8 milestone 2): out of scope
BY KIND, not by distance. Modelling `posix` to make `os` importable is
inventing an operating system, and this project's whole discipline is
that a construct it cannot model refuses loudly rather than guesses.

**The whole idea is worth single digits, and that is the number to put
beside its cost.** Closing `import` alone unblocks 7 files (`sole`,
above); a module system PLUS a computational-C surface reaches at most 8
more, three of them behind a Lean regex engine. That is a multi-session
build for ~15 of 167 files — while the tail that blocks the 208 LIBRARY
modules (`class-creation` 127, `Starred` 86, `Delete` 83, `With` 76)
moves modules by the dozen and is ordinary tier work.

**RECORDED CONSEQUENCE: `import` is not the next milestone either.** The
sole-blocker ranking correctly demoted the class tier and correctly
promoted `import`; measuring `import` now demotes it in turn. Neither of
the two biggest walls in the wild is worth building next, and knowing
that cost two instruments and no interpreter changes.

**AND IT PARTIALLY REHABILITATES THE CLASS TIER — with an ORDERING that
the naive reading of the two numbers gets backwards.** Among the 208
pure-Python modules a module system would have to run, `class-creation`
is the TOP blocker at 127, ahead of `Starred` (86), `Delete` (83), `With`
(76), `JoinedStr` (56), `Constant:bytes` (56), `Assert` (55). So the
class tier is worth ~1 file as a SEED tier and a great deal as a LIBRARY
tier. The ordering, stated so it cannot be misread:

1. its library value is REAL and it is the biggest single lever in the
   tail (below — adding it to the five named constructs takes the batch
   from 18 modules to 53);
2. but every bit of that value is BEHIND a module system, because these
   are modules nothing imports today;
3. and the module system is itself worth single digits (above).

The naive reading — 127 is the biggest number on the page, so build the
class tier — is the ordered-admission artifact wearing a new hat. `sole`
over the SEEDS says 0; `present` over the LIBRARY says 127; both are
true, and the second is only collectable after work that the first
section just priced out. Written down because someone will read those
two numbers again.

### The tail, ranked the same way — and it is a BATCH, not a ladder

Having killed two milestones on `sole`, the tail gets the same treatment
before anything is built (`import_closure.py --tier` now prints it):

**STATUS: construct 1 (`Assert`) is BUILT (2026-08-13, docs/memory-model.md
§the assert statement).** The counts in this section are the measurement
as taken BEFORE it landed and are deliberately left unedited — they are
the record that produced the sequencing rule below, not a live to-do
list. Read `Assert` here as historical, and the remaining tail as
`Starred`, `Delete`, `With`, `JoinedStr` plus `class-creation`,
`Constant:bytes` and `BinOp:BitAnd`.

* **No single construct in the tail is worth more than 5 modules on its
  own.** `sole` over the 188 blocked library modules: `class-creation`
  5, `JoinedStr` 4, `Starred`/`Delete`/`Constant:bytes`/`Assert` 3 each,
  `With` 2, `Set`/`DictComp`/`BinOp:RShift` 1, and `Global`/`Lambda`/
  `Constant:float`/`BinOp:Div` ZERO. Same shape as every ranking before
  it: `Starred` looks like 86 and is worth 3.
* **But the BATCH curve covers, and that is the difference from
  `import`.** These walls co-occur, and behind them there is no by-kind
  boundary — it is all ordinary Python. Greedy: 8 constructs free
  69/188, 11 free 108, 14 free 140 (74%). Named batches: the five
  language constructs (`Starred`, `Delete`, `With`, `JoinedStr`,
  `Assert`) free **18**; plus `class-creation` **53**; plus
  `Constant:bytes` and `BinOp:BitAnd` **82**.

### THE SEQUENCING PRINCIPLE (normative — read this before pricing any
### tail construct on its own)

The three findings above are a measurement. This is the RULE they imply,
written out because the next person to look at `Starred` in isolation
will otherwise reach the wrong conclusion exactly as the ordered-
admission ranking did twice before.

**1. No member of the tail may be justified by its own `sole` number.**
Judged that way every one of them is worth 2-5 modules, no single one
survives a cost-benefit test, and the conclusion is "build none of them"
— forever, no matter how many are left. That verdict is an artifact of
the unit of measurement, not a fact about the work. The unit is the
BATCH: 8 constructs free 69 of 188, 11 free 108, 14 free 140.

**2. The justification is LANGUAGE SURFACE, not the stdlib percentage.**
`Starred`, `With`, `JoinedStr`, `Assert` and `Delete` are ordinary Python
that real programs use. The standing goal is to verify ARBITRARY Python,
not to maximise a number over one corpus, so these are worth having
whether or not they move the sweep. That is a different and sounder
argument than the one that carried `import`, and it is the argument to
build them on. **The library counts SEQUENCE the work; they do not
justify it.**

**3. When the counts are all small and similar, sequence by PROOF-LAYER
SHAPE, with the count only as a tiebreak.** `assert` goes first not
because it is worth 3 modules but because it is the cheapest arm in the
interpreter: it evaluates two expressions and either does nothing or
raises, so it stays inside `Stmt.heapFree`, `worldInv` is undisturbed,
and only `fuelMono` and `clockErase` gain one arm each. A construct that
allocates, mutates, or retains state across a raise costs a fragment
change and should be sequenced later, whatever its count says.

**4. Prefer a construct whose semantics can REUSE an existing function
over one that needs a parallel table.** `assert`'s message renders
through `printOne`, the same function `print` applies to one argument —
because `str(x)` for an `AssertionError` argument and `str(x)` for a
`print` argument are the SAME CPython operation. Two tables that must
agree will drift; one function applied twice cannot. It also inherits
the pinned refusals (set, instance, non-ASCII) for free, which is the
same property on the negative cases. Look for that shape in every
remaining construct before writing a new renderer or a new walker.

### Two instrument fixes it required

* **`leanpy_survey.py --json` could not run at all.** `census` returned
  the wall set as a Python `set`, which `json.dump` refuses, so the
  survey's machine-readable output has raised `TypeError` on every
  corpus since the wall census landed (c90e662) — the ranking instrument
  built one commit earlier could not export the ranking. Walls are a
  sorted list now. Eight instrument failures of this shape across the
  lanes in two days: the measurement is the least-tested code we run.
* **The stdlib sweep's safety list was an unrecorded `--exclude`
  regex.** 167 = the 174 top-level `.py` files minus seven, and which
  seven was not written down anywhere, so the headline number was not
  reproducible. Pinned as `import_closure.SAFETY` (`antigravity`,
  `webbrowser`, `turtle`, `nntplib`, `smtpd`, `telnetlib`, `imaplib` —
  browser, window, network) and reachable as `leanpy_survey.py
  --stdlib`, which is still NOT in the default corpus: the decision that
  a routine harness run must never execute arbitrary stdlib top level
  stands, only the guesswork is gone. The reconstruction reproduces the
  recorded sweep exactly on every headline — 167 files, **5 MATCH, 162
  REFUSE, 0 DIVERGE**, `import` sole 7, `class-creation` sole 0 — with
  one number one off: `import` present is **154** here against the
  recorded 155. One file's wall set, on a list rebuilt from its
  description; it moves nothing, and it is written down rather than
  rounded to the number that was already on the page.

### Where the instrument can be wrong, stated

The closure is STATIC. 78 of the seeds reach `__import__` or
`importlib.import_module`, which no static walk can follow, so the true
closures are supersets of these — the C verdict can only get worse.
`if __name__ == "__main__":` blocks are counted for the SEED (leanpy
supplies `__name__`, so a file run as a program does execute them) and
NOT for anything below it (CPython skips them on import); getting that
wrong is what first gave `heapq` a dependency on `doctest`, `pdb`,
`unittest` and `signal`, and it inflated the C surface by three modules
before it was caught. `from p import x` is followed only when `p.x`
resolves to a module — otherwise `x` is an attribute of `p`, and
counting it would fake a hole.

The SECOND ceiling rides the extractor, which every harness runs under
`sys.executable` (3.14 here) and not under the pinned 3.9 — the exact
shape of the oracle bug found one commit earlier. CHECKED, not assumed:
the envelope census is identical under both interpreters on twelve
sample files spanning f-strings, class bodies, `Starred`, `Delete` and
walrus-free comprehensions — same node totals, same wall sets. The
extractor is a parser, not an oracle, and it is version-stable here.

AND THE TOOL IS TESTED AGAINST THE CASE IT IS SUPPOSED TO FAIL:
`--self-test` builds a synthetic module tree designed to make it answer
PURE and checks 13 rows — the pure two-hop chain, C at one hop and at
two, the `__main__` guard live for the seed and dead for its importer,
`from p import <attribute>` versus `from p import <submodule>`, a
function-body import that is whole-program only, a `try:` import that is
import-time but not unconditional, and the BFS depth (a depth-first walk
reports the wrong distance to C, which is what the frontier queue is
for). A tool that answered C-REACHING unconditionally would print this
section's headline unchanged and be worth nothing. Every verdict is also
auditable one at a time: `--why
MODULE` prints the import chain from a seed to each C module it reaches.

## `mvcgen` — SPIKED AND DECLINED, on shape, not on taste (2026-08-13)

Owner-asked: does leanpy use something like `mvcgen` to keep the proof
layer streamlined? Honest answer BEFORE the spike: partially — `@[spec]`
is applied in 34 places (15 in `LeanModels`, chiefly `Logic` and
`Surface`; 19 more across the `Examples/*/spec.lean` files), and
`VC.lean`'s `PyPost` explicitly mirrors `Std.Do`'s `PostCond`-with-shapes
idea — but VC generation is OUR OWN, not `Std.Do`'s (see THE GENERATOR
ALREADY EXISTS below; "hand-rolled" means purpose-built and maintained,
NOT missing). Scoped as a spike with one falsifiable question: can
`mvcgen` be driven against `PyTriple` at all, on ONE small construct?

**AVAILABILITY IS NOT THE OBSTACLE.** `mvcgen` ships in the pinned
toolchain (v4.33.0-rc1): `Std/Tactic/Do/Syntax.lean` declares the tactic,
`Lean/Elab/Tactic/Do/VCGen.lean` implements it, `Std/Do/{Triple,PostCond,
WP}.lean` are all present. It was tried, not guessed at.

**THE SPIKE, RUN AGAINST THE SMALLEST RULE IN THE LAYER.**
`PyStmtTriple.pass` — real proof 4 lines — restated as a goal and handed
to `mvcgen`:

    error: failed to synthesize
      Std.Do.SPred.Tactic.PropAsSPredTautology (PyStmtTriple m P (Stmt.pass sp) Q)

**And the second probe is the one that decides it.** The same goal with
the threshold written out by hand — `∀ st, P st → ∃ t, ∀ F ≥ t, Q.holds
(execStmt m F st (.pass sp))` — fails IDENTICALLY. So the obstacle is not
that `PyTriple` is an opaque abbreviation the tactic could be taught to
unfold. **It is the SHAPE.** `Std.Do.Triple` is `P ⊢ₛ wp⟦x⟧ Q` and the
only instance supplying `PropAsSPredTautology` is the one for that
triple, over `x : m α` with a `WP m ps` instance. Three things are
missing at once, and each is load-bearing:

1. **`Run` is not a monad.** It is a plain `inductive Run (σ α)` with a
   hand-rolled bind (`⤳`), no `Monad` instance and no `WP` instance. The
   repo never imports `Std.Do`; it cites it in a comment as inspiration.
2. **The verification object is DATA, not a program.** `mvcgen`
   symbolically executes a monadic term `x`. leanpy verifies
   `execStmts m F st ss` where `ss : List Stmt` is a Python AST. That is
   the definitional-interpreter design, on purpose — the thing being
   verified is arbitrary Python, which cannot be a Lean monadic term.
3. **The fuel threshold has nowhere to live.** `∃ t, ∀ F ≥ t` is chosen
   so triples compose through `fuelMono` (`PyTriple.exec` extracts one
   decided outcome valid at every larger fuel). `wp⟦x⟧ Q` has no
   counterpart, and quantifying outside the wp is exactly what the failed
   second probe shows the tactic cannot see.

**Obstacle 2 was never reached, and that is reported rather than
claimed.** `PyPost.holds` sends `.timeout => False` and `.unsupported _
=> False`, which is what makes the triple TOTAL correctness and an
out-of-tier program's triple unprovable. Whether an integration would
preserve it is untested, because obstacle 1 blocks first. No conclusion
is offered on a test that did not run.

**THE GENERATOR ALREADY EXISTS — read this before concluding anything
from the paragraph below.** `py_vcgen` is a BUILT, TESTED, THREE-LAYER
stack, not an aspiration: `VC.lean` (layer 1, the triples, 546 lines),
`VC2.lean` (layer 2, the loop rule and the `@[py_spec]` interprocedural
registry, 706), and **`LeanModels/Python/VCTactic.lean` (layer 3 — the
walker tactic itself, 2403 lines)**, whose entry point is a real tactic,
`elab "py_vcgen" "[" progs:ident,+ "]" cls:pyVcgenClause* : tactic`
(VCTactic.lean:2311). It does the mvcgen-shaped things: delayed goals for
loop invariants, measures and exit clauses over named Python-variable
telescopes, and symbolic-execution discharge of the interpreter
obligations. It is regression-tested through recursive factorial
(`VCTests.lean`, with `#guard factorial 5 = 120` and a `@[py_spec]`
callee spec consumed by a caller), and has been maintained through pass 8.
So the honest headline is NOT "there is no VC automation here". It is:
**stock `mvcgen` adds nothing because this project already built its own
generator, and that one fits the architecture — a deep embedding over AST
data with a fuel-threshold triple — which is exactly what the stock one
cannot reach.**

**WHAT WOULD IT SAVE — the part that actually decides it.** Nothing that
matters, for two independent reasons. The per-program layer is ALREADY
AUTOMATED by `py_vcgen` above, so there is no gap there to fill. And the
only remaining bulk is `Obs.lean` (3024 lines) and `ClockErase.lean`
(2587), whose content is hand-rolled 18-conjunct MUTUAL INDUCTIONS over
the `Stmt`/`Expr` AST proving meta-theorems (`fuelMono`, `worldInv`,
clock erasure) for ALL Python programs at once. `mvcgen` is a per-program
VC generator: it discharges one program's verification conditions. It has
categorically nothing to offer an induction over the interpreter's own
definition. A fully successful integration would therefore leave those
5611 lines untouched and duplicate 3655 lines that already work.

**And the tool says so itself:** every invocation emits `The mvcgen
tactic is experimental and still under development. Avoid using it in
production projects.` A development whose entire value is that it is
sound does not put an experimental VC generator under its proof layer to
save nothing.

**THE SV SIDE, ASKED AT THE SAME TIME AND ANSWERED SEPARATELY.** The two
surfaces are NOT at the same maturity and should not be described as if
they were. On the Python side there is a walker tactic (`py_vcgen`,
above). On the SV side there is **`#sv_check`** — a COMMAND, declared in
`LeanModels/Sv/Surface.lean`, giving concrete-run guards in surface
syntax (`#sv_check counterD [[clk := 1, rst := 1], [rst := 0]] shows
count = [0, 1]`), i.e. `%b`-column checks of completed runs. **There is no
SV walker tactic**: `LeanModels/Sv/` contains no tactic declaration at
all. So SV today has a concrete-run guard surface, not a VC generator.
That is a statement of current scope, not a promise to build one.

**DECLINED** — the third well-argued no, after the inheritance tier and
`import`. Recorded with the probe that produced it so the next person
re-runs the measurement instead of re-deriving the argument. **This entry
is not a licence to build a VC generator: one exists (`VCTactic.lean`).**
Revisit `Std.Do` only if `Run` acquires a genuine `WP` instance AND the
threshold form is expressible inside it — and even then, only where it
would BEAT `py_vcgen`, never as a migration of anything that compiles.

## The tail, construct 3: `del <name>` DESIGNED as a SLICE (2026-08-13)

Design only. Nothing here is built, and nothing here registers a harness
row — registrations land WITH the implementation (b921f32). The construct
2 (f-strings) landing is HELD upstream of this and is not chained to it.

### The slice, stated before the argument for it

**`del <name>`, locals-only, function scope only.** `del d[k]`,
`del o.attr`, `del xs[0]` and MODULE-scope `del` stay LOUD. That is not
a convenience boundary; each excluded form is a measured second table,
and §the measurement below names which.

### The earlier ranking was WRONG about `Delete`, and the definitions say so

§THE SEQUENCING PRINCIPLE priced `Delete` out with: "`del x` removes a
binding and no `Env` removal primitive exists; `del d[k]` mutates the
heap. Both mean `worldInv` must be re-established — a fragment change."
The second clause is true. **The first is false**, and the file that
settles it is `LeanModels/Python/Runtime.lean`:

```
structure World where          -- Runtime.lean:195
  heap : Heap
  globals : REnv
  stdout : …
structure FrameState where     -- Runtime.lean:224
  world : World
  locals : REnv
```

`locals` is NOT a `World` field. `worldInv` is `Run.OkW (·.world = st.world)`,
so a statement that only rewrites `st.locals` preserves it **by
construction** — the identical situation as `assign` to a bare name,
which is already in the fragment. The ranking conflated `del x` with
`del d[k]`; separating them is the whole content of the slice. The
missing `Env.remove` is real but it is three lines of structural
recursion on `List (String × α)` next to `Env.lookup`/`Env.set`
(Semantics.lean:580-588), not a fragment change.

Priced against the definitions, not predicted:

* `Stmt.heapFree` — the `del` arm is unconditionally `true`. `del <name>`
  evaluates NO sub-expression (measured: `r9`), so there is nothing to
  recurse into and no new exclusion.
* `worldInv` (Obs.lean) — the `.okF h _` shape, per the structures above.
* `ceExecStmt_succ` (ClockErase.lean) — `Env.remove` reads neither heap
  nor clock, so the arm is `.ok hs _` with **no `ce_norm`**. (That is a
  live distinction, not a formality: `ce_norm` is exactly what a
  heap-READING arm needs, and its absence is what makes `case bstr` a
  defect after the `str` widening — see the f-strings review.)
* `fuelMono` — no recursion, no fuel: `Run.le_refl`.

Three proof sites, all trivial arms. **Cheaper than `assert`**, which
needed a `bind`, an `ite` and a `printOne` case-split on every one of
them. This is the definition of a slice.

### The measurement (CPython 3.9.19, run before this was written)

| shape | source | CPython 3.9.19 |
|---|---|---|
| read after del | `x = n; del x; return x` | `UnboundLocalError: local variable 'x' referenced before assignment` |
| rebind after del | `x = n; del x; x = 99; return x` | `99` |
| del a module-global NAME | `del g; return 0` | `UnboundLocalError` — `del` LOCALISES `g` |
| read BEFORE that del | `y = g; del g; return y` | `UnboundLocalError` at the READ — localisation is whole-body |
| `del x, y` | `x = n; del x, nosuch` | left-to-right, and **PARTIAL**: `x` really is gone when `nosuch` raises |
| del of unbound / double del | `del nope` / `del x; del x` | `UnboundLocalError` |
| del a parameter | `del n; return 0` | `0` |
| del a parameter, then read | `del n; return n` | `UnboundLocalError` |
| conditional del | `if n > 0: del x` then read | raises only on the taken path |
| loop del + rebind | `for i: x = i; del x; x = i*2` | `6` for `n = 3` |
| MODULE scope | `b = 5; del b; print(b)` | **`NameError: name 'b' is not defined`** |
| MODULE scope, unbound | `del never` | `NameError` |
| the class | `UnboundLocalError.__mro__` | `(UnboundLocalError, NameError, Exception)` |

Two rows decide boundaries on their own. **Module scope answers a
DIFFERENT exception class than function scope** — `NameError`, because
module locals ARE the globals (§the publish) — so admitting it means
carrying a second table for the same keyword; it is refused. And
**`del x, y` is partial**, so the runtime arm must thread state through
the targets left-to-right and may not decide the whole statement up
front.

### THE FIRST DECISION: the read-after-del fallthrough, closed by CENSUS

The hazard: `Env` is `List (String × RVal)` with `lookup`/`set` only. Take
the entry out and the name is simply GONE — indistinguishable from a name
that was never local. The next read of it falls through to
`moduleGlobals` and then `World.globals`, so `del x; return x` would
answer a GLOBAL where CPython raises. Silently wrong, which this
development does not ship.

**Option A — a new `PyErr.unboundLocalError` — is REJECTED, and not for
the reason the option was framed with.** The exhaustive-match ripple was
priced and it is SMALL: `PyErr` is matched exhaustively in exactly two
places, `errName` and `errMessage`, both in `Main.lean`, both runtime
code with no theorem about them. If that were the cost, the option would
be cheap.

The real cost is that **the constructor does not solve the problem.** To
RAISE `UnboundLocalError` the interpreter must know the name is a local
of this frame that currently holds no value — and after a removal from a
`List (String × RVal)` that fact is not represented anywhere. Recovering
it needs one of:

* a tombstone value — an `Option RVal` env or a new `RVal` constructor,
  which touches every value-level match and adds a case to both
  18-conjunct mutual inductions. That is the `Constant:bytes` shape, the
  most expensive in the batch, which the sequencing principle already
  ranks last;
* or a new `FrameState` field (the deleted names, or the static local
  set), which changes the frame's SHAPE and therefore ripples into
  `worldInv`, `ClockErasedF`, `withClock`, `withLocals` and every
  `.okF`/`.liftResF` congruence — strictly worse.

So Option A is a frame-representation change wearing a constructor's
clothes. Rejecting it is what KEEPS this a slice; taking it would make
`Delete` the dearest construct in the tail rather than the cheapest.

**Option B — the extractor census — is CHOSEN**, and the deciding point
is that it is not a new mechanism. `locals_unsupported` already exists
and already carries exactly this hazard, twice, in the extractor's own
words: `_shadowed_calls` ("CPython would treat the callee as an
(initially unbound) local, so a dynamic-env interpreter cannot be
faithful") and `_early_nested_calls` ("such a call raises
UnboundLocalError — a dynamic-env fallthrough to a module name would be
silently wrong"). **`del` is the THIRD instance of the hazard the channel
was built for.** Reuse over a parallel table, one construct later — the
same criterion that made `assert` and f-strings cheap.

There is even an existing INCONSISTENCY the census repairs rather than
extends: `_binding_linenos` (extract.py:586) ALREADY counts `ast.Delete`
targets as bindings; `_assigned_names`, which routes through
`_target_bound_names`, does not. The two functions disagree today. The
census makes them agree.

### The census, exactly (all syntactic — no dataflow, which is the point)

1. **`del` targets bind.** `_assigned_names` gains `ast.Delete`, so a
   `del`'d name is local THROUGHOUT the body — CPython's own whole-body
   rule, measured above, reused rather than re-derived. This also makes
   `_shadowed_calls` and `_early_nested_calls` see `del`'d callee names
   for free.
2. **A new `locals_unsupported` clause:** if any `del` target name is
   READ anywhere in the body (an `ast.Name` in `Load` context), refuse
   the function. Loud.
3. Module-scope `Delete` → `Unsupported` (row 11 of the measurement).
4. Any target that is not a bare `ast.Name` → `Unsupported`.

Clause 2 is deliberately a NAME-SET intersection and deliberately not a
liveness analysis. Deciding "is this read reachable from that `del`
without an intervening bind" is CPython's definite-assignment rule
re-implemented in the extractor: a parallel table, refused on the same
grounds the f-string format mini-language was refused. **The stated
price** is that `x = n; del x; x = 99; return x` and the loop
del-then-rebind row REFUSE although CPython accepts them. That is an
over-refusal, it is honest, and it is written down here so the next
reader does not rediscover it as a bug.

### The runtime arm, and why it needs no new error

`execStmt`'s `delStmt` arm folds the names LEFT TO RIGHT (row 5 of the
measurement — the effect is partial, so the fold must thread the state):
`Env.lookup st.locals n` gives `some _` ⇒ `Env.remove`; `none` ⇒
`.unsupported`, LOUD, with the earlier removals already applied, which is
CPython's order.

The `none` case is where CPython raises `UnboundLocalError`, and the
model **refuses instead of inventing a class**, the same call `errMessage`
already documents for the payload-free constructors ("Never invent one
here"). This is what retires the new `PyErr` entirely: with clause 2 in
force, no admitted body ever reads a deleted name, so the only way to
reach the `none` case is `del` of a name that was never bound — the
`del g` / `del nope` / double-`del` rows.

Note the layering, which is the design's shape in one sentence: **the
READ hazard is closed statically because the runtime cannot see it, and
the DELETE hazard is closed dynamically because the runtime sees it
EXACTLY.** Neither layer approximates what the other decides, so neither
needs a table of its own.

### Surface added

One `Stmt` constructor (`delStmt (names : Array String) (sp : Span)`),
`Env.remove`, one `execStmt` arm, the same five walkers `assert` touched,
one `Json.lean` ingestion arm, and the four extractor clauses above.
Open at implementation time, to be MEASURED not assumed: `Stmt.g1Binds`
is `[]` and `Stmt.g1Dirty` should be `true` conservatively — module-scope
`del` is refused by clause 3, so the constructor cannot appear at top
level, but the walkers must still be total.

### Battery to build (rows measured above; registered WITH the code)

`Examples/python/del_lab` — in tier: `del` of a local never read after,
`del` of a parameter, `del x, y` of two unread locals. Refused by census:
read-after-del, rebind-after-del (the stated over-refusal, pinned so the
cost stays visible), loop del-then-rebind. Refused at runtime: `del g` of
a module-global name, `del` of a never-bound name, double `del`. Refused
by shape: `del d[k]`, `del o.attr`, module-scope `del`. Plus a script
whose stdout is compared byte-for-byte.

## `del` RECONCILED with the one pipeline: the module-scope arm (2026-08-14)

The recorded design above is implemented as written for FUNCTION scope —
census clauses 1, 2 and 4, `Env.remove`, the left-to-right partial
runtime arm, the three trivial proof sites. This section records the ONE
revision (clause 3), why the post-one-pipeline world changes its price,
and two open notes the recorded design asked to have MEASURED. Written
BEFORE implementing; the flip prediction below is pre-registered.

### The conflict, named

The paying consumer is `opcode.py` — the stdlib sweep's only reachable
`del` payer (measured 2026-08-14: `quopri.py` contains ZERO `del`
statements, so "quopri/opcode stand on del/bytes" distributes as quopri →
bytes, opcode → del; `types.py`'s `del sys, _f, …` sits behind many other
walls; `copyreg.py`'s dels are subscript form, excluded by clause 4
unrevised). Its one `del` is `del def_op, name_op, jrel_op, jabs_op` —
MODULE scope, targets all top-level `def` names, the module's LAST
statement. The recorded clause 3 refuses exactly this.

### Why the refusal's price changed

The recorded reason was "module scope answers a DIFFERENT exception class
(`NameError`) — a second table for the same keyword." Post-one-pipeline
that table already EXISTS: Script.lean is the established second-table
site (the import-handler table, the `NameError` exit-1 surface), and by
§the publish a module frame's locals ARE its globals — so the module-scope
arm is one `execScriptOne` arm over `st.locals`, OUTSIDE the mutual block
and outside all three 18-conjunct inductions. The recorded design's
STOP-condition (frame-shape or value-level machinery) is not triggered:
the interpreter change is still exactly the recorded `execStmt` arm plus
`Env.remove`.

### Measured rows the arm is built on (CPython 3.9.19, 2026-08-14)

| shape | CPython | model decision |
|---|---|---|
| `del len` (a builtin, module scope) | `NameError: name 'len' is not defined` | deciding `NameError` on a locals miss is FAITHFUL even for builtin names — deletion never consults builtins, so this arm does NOT need the `isPyBuiltinName` consult the READ arms need |
| `del __name__` then `print(__name__)` | prints `builtins` (the deleted module global UNCOVERS the builtins module's own `__name__`) | dunder targets refuse LOUDLY — the model's dunder arm resolves reads statically, so a removal would be silently ignored |
| `import time` then `del time` | exit 0, silently | benign-import names bind STATICALLY in the model (never in locals), so the removal has nothing to act on — refuse LOUDLY |
| `def f: …; print(f(1)); del f` (trailing) | exit 0 | the ingestion rewrite below |
| `del f; del f` (def name, twice) | `NameError` on the second | uniqueness census below — neither is rewritten, runtime refuses loudly |
| `del f, x, nosuch` (trailing; f a def) | f and x gone, then `NameError: name 'nosuch' is not defined` | per-target filter + partial left-to-right runtime |

### The module-scope arm, exactly (Script.lean, `execScriptOne`)

Per target, left to right, threading `st.locals` (the partial-effect rule
of the recorded measurement, now with retained state on the raise):
locals HIT → `Env.remove`, continue; MISS → dunder-shaped → loud;
benign-import-bound → loud; `def`/`class`/namedtuple name → loud (the
trailing rewrite below is the only admission); otherwise the faithful
`.exn (.nameError n)` — module locals are COMPLETE under the one pipeline
(nothing is skipped or stale), so the miss IS CPython's NameError, the
same authority the exit-1 surface already claims. Inside a delegated
`while … else` a module-scope `del` falls to `execStmt`'s function-scope
arm: a hit removes (locals are the frame's), a miss refuses loudly —
sound, and `Stmt.assignedNames` gains the del targets so
`scriptFlushCoherent` sees mid-compound removals like mid-compound binds.

### Trailing `del` of definition names: an INGESTION rewrite (the aliasing precedent)

A `def`/`class`/namedtuple binding is a STATIC table entry, not a runtime
value; no runtime arm can remove it without tombstone machinery (the
recorded Option A, still rejected). But the paying shape needs no runtime:
in the module's TRAILING RUN (the maximal suffix of top-level statements
that are all `Delete` or `Pass`), a del target that is a definition name
is dropped from its statement at ingestion (a statement left with no
targets becomes `pass`), provided that name occurs as a del target
EXACTLY ONCE in the whole top level (nested compounds included — the
uniqueness census that keeps `del f; del f` loud). Soundness: a
definition name is CERTAINLY bound there (`defsBoundBefore` orders the
mention, `initBindable` forbids rebinding, uniqueness forbids an earlier
admitted del), so its deletion cannot raise and — being in the trailing
run — cannot be observed: every statement after it is a del or pass, and
an exception from a REMAINING target aborts both sides identically.
Dropping def-name targets therefore preserves CPython's partial
left-to-right order exactly. Non-trailing del-of-def stays loud at
runtime. Placement: after `recognizeDefAliases` (alias entries are
functions entries, so `del bisect` of an alias is covered by the same
test).

### The recorded design's two open notes, MEASURED

* **`Stmt.g1Binds` must be `some targets`, NOT `some []`.** The closed
  -function surface executes fold-refused top-level statements through
  `initExecStmt` with EMPTY locals, so a top-level `del` always refuses
  there and takes the rollback-and-poison path — and `globalsDirty`
  poisons exactly `g1Binds ++ g1Stores`. With `[]` the deleted name's
  STATIC binding would survive the rollback and a later read would answer
  a stale value where CPython raises: silently wrong. With the targets in
  `g1Binds` the name is poisoned and every later read refuses loudly.
  (This also keeps the extractor agreement the design demanded:
  `_binding_linenos` already counts `Delete` targets; `_assigned_names`
  now does too.) `g1ExecCandidate` is `true` — the `raise`/`assert`
  argument verbatim.
* **Mention censuses see del targets as names.** `stmtRefs`,
  `stmtNamesXW`, `yfNames`, `Stmt.allNames` all gain the target list —
  the conservative direction everywhere it feeds (`defsBoundBefore`
  ordering, namedtuple/alias censuses, capture censuses).

### PRE-REGISTERED flip prediction (written before building)

**opcode.py does NOT flip on this landing.** Its static wall set is
`{Delete}` (sole), but the static census cannot see DYNAMIC refusals —
the `sole` ranking's known instrument limit, met again. Reading the
source in execution order: the guarded `from _opcode import stack_effect`
is landed Pass 0 surface (the try body's `__all__.append` is dead under
the model's except path — the recorded §2.5 divergence); `__all__ = […]`
is a plain in-tier bind; then line 36, `opname = ['<%r>' % (op,) for op
in range(256)]`, hits `evalBinOp`'s `.mod, .str` arm — `"'%' string
formatting is outside the v0 tier"`, a LOUD dynamic refusal confirmed by
probe against the laptop binary (stale-binary caveat noted; the arm is
unchanged on master). Predicted survey outcome: wild sweep stays
7 MATCH / 159 REFUSE, flip set EMPTY, 0 DIVERGE; opcode's refusal
MESSAGE moves from `unsupported statement 'Delete'` to the `%`-formatting
refusal (that message movement is the acceptance signal that `del`
itself cleared). The honest chain to the opcode flip is therefore
del (this landing) + a `%`-formatting slice (`str % (int,)` under
`%r`/`%d` is buildable on the shipped `reprVal`; not designed here, not
this lane's scope). If opcode DIVERGES or refuses on anything OTHER than
the `%` arm, that is a finding.

### Battery beyond the recorded rows (module scope, script surface)

`del`-bound-then-read → `NameError` exit 1; `del never` → `NameError`;
trailing del-of-def (the opcode-shaped fallback script: defs, mutating
calls, prints, trailing `del`) → MATCH; non-trailing del-of-def → REFUSE;
`del __name__` → REFUSE; `del time` after the benign import → REFUSE;
mixed trailing `del f, x, nosuch` → `NameError` with f and x really gone.

## The tail, construct 4: ranked (2026-08-13)

**STATUS: `BinOp:BitAnd` is DESIGNED — see §the bitwise family below.**
The ranking here is the record that produced that choice and is left
unedited.

By §THE SEQUENCING PRINCIPLE — proof-layer shape first, counts only as a
tiebreak. Measured positions in the source, not recalled:

1. **`BinOp:BitAnd` — the cheapest thing left, and it beats `Starred`.**
   `evalBinOp` is at Semantics.lean:475, **outside every `mutual` block**
   (the neighbouring blocks close at 391 and open at 1031). So the whole
   construct is one constructor on an inductive that already carries
   `lshift | bitOr` (Ast.lean:26-28), one `evalBinOp` arm, one
   `ALLOWED_BINOPS` entry, one `Json.lean` string. The `binOp` arm of
   every walker and every proof ALREADY recurses structurally and is
   indifferent to which operator it holds: **zero new proof arms**, the
   f-string result reached by a different route. Pass 5 already admitted
   `<<` and `|` for the shipped sunfish file, so this completes a set
   rather than opening one.
2. **`Starred`** — ALLOCATES (unpacking builds a sequence) and reaches
   into the call machinery; `worldInv` moves.
3. **`class-creation`** — a tier, not a construct.
4. **`Constant:bytes`** — a new `RVal` constructor: every value-level
   match plus a case in both 18-conjunct mutual inductions. Dearest of
   the value-level work.
5. **`With` — LAST, and it is not close.** It retains state across a
   raise, it sits behind the class tier, and there are ZERO runnable
   programs for it today. Nothing is learned by moving it earlier.

Recommended order: `del` (designed above), then `BitAnd`, then `Starred`.

## The tail, construct 4: `BinOp:BitAnd` DESIGNED — and the measurement RETIRES `|`'s negative refusal (2026-08-13)

### The design, stated before the argument for it

`&` is admitted with its FULL int semantics, negative operands included,
because negative operands turn out to be EXACT in core Lean and the
pass-5 refusal that said otherwise was a design-time prediction, not a
measurement. The value tier is one new function, `intBitwise`-shaped,
applied to `&`, `|` and `^` alike — one function three times, never
three tables (§THE SEQUENCING PRINCIPLE, rule 4).

### Zero new proof arms — VERIFIED at the arms, not inferred from the ranking

The ranking above ASSERTED this. It is now checked at every site, by
grep over the source rather than by recall:

* `evalBinOp` is at Semantics.lean:475. The `mutual` blocks around it
  close at 391 and open at 1031, so it is outside every one of them.
* Every walker binds the operator and drops it: `Expr.heapFree`
  (Semantics.lean:3348), `genAllocFree` (3498), `g1HeapPure` (2898) and
  `Script.allNames` (Script.lean:128) all spell the arm
  `| .binOp l _ r _ => …`; `nodeKind` (189) is `| .binOp .. =>`.
* **All three expensive proof sites treat `evalBinOp` as OPAQUE.**
  `fuelMono` (Obs.lean:501), `worldInv` (Obs.lean:2053) and
  `ceExecStmt_succ` (ClockErase.lean:1350) each `.bind` the two operand
  IHs and then discharge the operator with `.liftRes`/`.liftResF`,
  which is generic over the whole `Res` — `.ok`, `.exn` AND
  `.unsupported`. None of them cases on `op`; none of them unfolds
  `evalBinOp`. A new arm with a new refusal cannot reach them.
* `Obs.lean` and `ClockErase.lean` contain **no `.binOp` occurrence at
  all** — only the three bound-variable arms above. There is no operator
  table anywhere in the proof layer to keep in sync.
* The three `.binOp`s in VCTactic.lean (2350, 2351, 2363) are TEST
  FIXTURES that construct terms, not a dispatch table.

So the f-strings outcome is reached by a second, independent route: the
proof layer does not move.

### The measurement (CPython 3.9.19, run before any of this was written)

`/opt/homebrew/bin/python3.9`, `Python 3.9.19`. Rows, verbatim:

* **Plain ints.** `12 & 10 → 8`, `0b1011 & 0b1101 → 9`, `255 & 0 → 0`,
  `((1<<100)-1) & 0xff → 255`.
* **Boolness, all four cells.** `True & True → True`,
  `True & False → False`, `False & True → False`,
  `False & False → False`, every one a `bool`. One int operand makes it
  an int: `True & 1 → 1`, `1 & True → 1`, `True & 3 → 1`,
  `3 & True → 1`, `True & 0 → 0`, and `type(0 & True)` is `int`.
  Identical to `|`'s pinned table.
* **Negative operands do NOT raise — they have values.** `-1 & 3 → 3`,
  `3 & -1 → 3`, `-2 & 3 → 2`, `-1 & -1 → -1`, `-4 & -3 → -4`,
  `-1 & 0 → 0`, `-5 & 12 → 8`, `12 & -5 → 8`, `-3 & -5 → -7`,
  `-16 & 15 → 0`, `-100 & 7 → 4`.
* **Type errors, verbatim** — and they are exactly the string the
  existing fallback arm already builds from `op.symbol` and
  `typeName`: `unsupported operand type(s) for &: 'int' and 'str'`,
  and the same with `'str'`/`'int'`, `'NoneType'`, `'list'`,
  `'tuple'`, `'dict'`, `'bool'`/`'str'`, `'range'`/`'int'`, and
  `'Move'`/`'int'` for a namedtuple — which is the CLASS name, matching
  `RVal.typeName`'s `| .ntuple tn _ _ => tn`.
* **`{1} & {2}` is `set()`, NOT a TypeError.** Set intersection. This is
  the one trap in the row set, and the model ALREADY survives it: sets
  are `Obj.pyset` on the heap (Runtime.lean:187), so a set operand is a
  `.ref`, and `evalBinOp`'s `.ref` arm fires BEFORE the `TypeError`
  fallback and refuses loudly. No new arm, no fake `TypeError`. (The
  refusal message's prose says "dict operators"; that is a wording nit
  on a correct refusal, not a defect.)
* **No short-circuit.** Both operands are evaluated, left first, and a
  raising right operand still raises after the left has run — which is
  precisely the `.bind l (.bind r)` shape `evalExpr` already has.
* Floats are unreachable: `Constant:float` is refused by the extractor,
  so `1 & 1.0` never reaches the interpreter.

### THE DECISION: negatives COMPUTE. They do not refuse.

Pass 5 refused a negative `|` operand on the stated ground that
"infinite two's complement is not guessed". Nothing needs to be guessed.
Lean's `Int` is ALREADY in the complement representation: `Int.negSucc n`
IS `-(n+1)`, so for a negative `x` the number `-x-1` — whose bits are the
complement of `x`'s — is the constructor's own argument, available by
matching and requiring no arithmetic whatsoever. Each operator becomes a
four-way match on the two constructors over core `Nat.land`/`Nat.lor`/
`Nat.xor` (`@[extern]`, Init/Data/Nat/Bitwise/Basic.lean:99-101):

```lean
/-- `a &&& ~m` over `Nat`. `Nat.ldiff` does not exist in v4.33.0-rc1, and
none is needed: every bit of `a` either is or is not in `m`, so removing
the ones that are IS the difference. Never underflows. -/
def ndiff (a m : Nat) : Nat := a - (a &&& m)

def intAnd : Int → Int → Int
  | .ofNat a,   .ofNat b   => .ofNat (a &&& b)
  | .negSucc a, .ofNat b   => .ofNat (ndiff b a)
  | .ofNat a,   .negSucc b => .ofNat (ndiff a b)
  | .negSucc a, .negSucc b => .negSucc (a ||| b)

def intOr : Int → Int → Int
  | .ofNat a,   .ofNat b   => .ofNat (a ||| b)
  | .negSucc a, .ofNat b   => .negSucc (ndiff a b)
  | .ofNat a,   .negSucc b => .negSucc (ndiff b a)
  | .negSucc a, .negSucc b => .negSucc (a &&& b)

def intXor : Int → Int → Int
  | .ofNat a,   .ofNat b   => .ofNat (a ^^^ b)
  | .negSucc a, .ofNat b   => .negSucc (a ^^^ b)
  | .ofNat a,   .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)
```

Mathlib-free, which the Python model requires (`LeanModels/Python`
imports `LeanModels.Core.Basic` and nothing from Mathlib; the only
Mathlib contact in the tier is the `sorted` proof harvest).

The `evalBinOp` arm is then the `bitOr` arm's shape with the refusal
deleted — boolness decided FIRST, because `bool op bool` returns a
`bool` and any int operand makes it an int:

```lean
| .bitAnd =>
    (match a, b with
     | .bool p, .bool q => .ok (.bool (p && q))
     | _, _ => .ok (.int (intAnd x y)))
```

**Why this is not gratuitous.** The honesty discipline is "fake
exceptions never, `unsupported` for anything CPython would handle
differently". `.unsupported` earns its place where CPython WOULD differ.
Here it does not differ: the value is exact and now derived. Keeping the
refusal would be manufacturing a refusal for a case known to be right —
the mirror image of manufacturing a green triad.

### The instrument that checked the formula, and its falsification test

The formula was NOT verified by reading eleven rows. Both the general
form and the `negSucc`-shaped form above were executed against CPython
3.9.19 over a grid (`-64..64` plus 255/256/1023/4096, `10**12`,
`10**18+7`, `1<<63`, `1<<100`, `(1<<100)-1`, `(1<<64)+12345` and every
negation) for all three operators:

    pairs=22201  ops=66603  FAILS=0
    ndiff underflows = 0            (must be 0 — Nat subtraction truncates)
    self-test (one arm broken) mismatches = 5402   (must be > 0)

The self-test is the point: an instrument that cannot fail is worth
nothing, so one arm was deliberately given the wrong Nat operator and
the grid caught it 5402 times. An earlier, differently-written candidate
(sign tests plus `abs`, no constructor match) was checked against the
same grid independently and also passed at 27075 checks, so the result
does not ride on one encoding.

**`#guard` reducibility — MEASURED, and it was the one real risk.**
`Nat.land` is well-founded recursion over `Nat.bitwise`, which the
KERNEL does not reduce with GMP the way it does `+`/`*`/`decEq`, so
`decide`-style evaluation was the thing that could have sunk this. It
does not apply: `#guard` is elaborated by `evalGuardCmd`
(Lean/Elab/Tactic/Guard.lean:154-166), which calls `unsafe evalExpr Bool`
— the COMPILER, where `@[extern "lean_nat_land"]` is the GMP builtin. The
Tests.lean battery evaluates natively. The residual risk is narrow and
named: a `@[py_spec]` user who discharges `evalBinOp .bitAnd a b = .ok r`
by `decide` in the KERNEL may find it does not reduce. No such spec
exists today, and `rfl`-by-native-decide or an explicit
`intAnd`-value lemma is the escape if one is written.

### What this does to `|` — a MEASURED CORRECTION, with one registered row

Landing `&` with computed negatives while `|` still refuses them would
install the exact drift rule 4 warns about, inside a single family, in a
single change. So `intOr` replaces `bitOr`'s refusal in the same
landing. Consequences, stated:

* Semantics.lean:503-510's `.unsupported` for a negative `|` operand
  goes away. Its message ("infinite two's complement is not guessed")
  is retired as measured-wrong in the same sense as `msg_nonascii`.
* **`harness/cases.json` `seq_lab.bor_neg` is registered
  `"expect": "unsupported"`** (line 429 at HEAD). It becomes
  `"expect": "match"` — one fewer unsupported row, which TIGHTENS the
  suite exactly as the assert correction did. `Examples/python/
  seq_lab/seq_lab.py:207-211`'s comment ("a negative operand: loudly
  out") is corrected with it, and the function is kept, now as a
  positive row.
* Nothing else moves: `shl`'s row already carries `[-3, 4]`, so the
  SHIFT family has always computed negative operands exactly
  (`x * 2^n`). The asymmetry being removed here is one that pass 5
  introduced between two halves of its own landing.

This is a behaviour change to landed, reviewed semantics. It only ever
turns a refusal into a measured-correct value — it can never turn a
right answer into a wrong one — but it is called out here rather than
buried, and it is the one part of this design an owner might reasonably
split off. If it is split off, `&` must take the REFUSAL branch and
match `|`; the two must not disagree.

### `^` rides free. `>>` does NOT, and `<<` has a pre-existing hole.

**`BitXor` is a rider, and separable.** With `intXor` written, `^` costs
one `Ast.lean` constructor, one `Json.lean` string, one `BinOp.symbol`
arm, one `ALLOWED_BINOPS` entry and one `evalBinOp` arm — no new design
surface at all. Measured and in tier: `12 ^ 10 → 6`, `True ^ True →
False` and `False ^ False → False` (both `bool`), `True ^ 1 → 0` (int),
`-1 ^ 3 → -4`, `-2 ^ -3 → 3`, `5 ^ -1 → -6`; `{1} ^ {2} → {1, 3}` is set
symmetric difference and is caught by the same `.ref` arm as `&`.
Recommended in, but droppable without touching anything else.

**`RShift` is NOT in this landing.** It belongs to the shift family, not
the bitwise family, and it has its own unresolved decision. Measured:
`12 >> 2 → 3`, `-7 >> 1 → -4`, `-8 >> 1 → -4`, `-1 >> 100 → -1`,
`1 >> -1 → ValueError: negative shift count`. Every value row is exactly
`Int.fdiv x (2^n)` (checked over the same grid, 2565 shift rows, 0
failures), so the VALUE tier is trivial — but `type(True >> True)` is
**`int`, not `bool`**, which is the opposite of `&`/`|`/`^` and matches
`<<` (`type(True << True)` is `int` too). Predicting boolness from the
bitwise family would have been wrong; the shift family never returns a
bool.

The blocker is size, and it is shared with a **pre-existing hole in
`<<`**: `evalBinOp`'s `.lshift` arm computes `x * 2^y.toNat` with NO
bound on `y`. CPython raises `OverflowError: too many digits in integer`
for `1 << (10**30)` (measured; `1 << (10**9)` succeeds, bit_length
1000000001), whereas the model would sit down and try to build the
number — a hang, not a refusal, which is the one failure mode the
project does not tolerate. `>>` needs the same guard for the mirror
reason: `1 >> (10**30)` is `0` in CPython (and `-7 >> (10**30)` is `-1`),
but `Int.fdiv x (2^(10**30))` must never construct that divisor. The
exact saturation is available — once `2^y > |x|` the answer is `-1` for
negative `x` and `0` otherwise — so a bounded arm is writeable; it just
needs its own budget decision alongside `seqBudget`, and it should be
taken with `>>`, not smuggled in with `&`. **Recorded as a live defect
in shipped `<<`, not as a new one.**

### Surface added

One `BinOp` constructor (`bitAnd`, plus `bitXor` if the rider lands) on
an inductive that already carries `lshift | bitOr` (Ast.lean:26-28) and
its doc comment; three small `Int` functions (`ndiff`, `intAnd`,
`intOr`, `intXor`) beside `evalBinOp`; one `evalBinOp` arm per operator
plus the `bitOr` arm rewritten; one `BinOp.symbol` arm per operator
(Semantics.lean:161-169) — which is what makes every `TypeError` message
come out verbatim for free; one `parseBinOpName` string per operator
(Json.lean:70-79); one `ALLOWED_BINOPS` entry per operator
(extract.py:69-74). **Zero walker arms and zero proof arms.**

One entry buys BOTH forms: `ALLOWED_BINOPS` is consulted by the
`ast.BinOp` clause (extract.py:256-266) AND the `ast.AugAssign` clause
(extract.py:913-923), and CPython routes `a &= b` through the same
operator — measured: `a = 6; a &= 3` gives `2` (int), `b = True;
b &= True` gives `True` (bool), `d = 12; d ^= 10` gives `6`. So `&=`
and `^=` arrive with no extra work, the way `|=` did for `bound()`.

Open at implementation time, to be MEASURED not assumed: whether
`Tests.lean`'s `#guard`s over `intAnd` on `1 <<< 100`-scale literals stay
fast (they should — GMP — but time them rather than assume).

### Battery to build (rows measured above; registered WITH the code)

Extend `Examples/python/seq_lab` rather than opening a lab: pass 5's
`shl`/`bor`/`bor_aug`/`bor_neg` already live there and this completes
their set, which is the whole argument for the construct.

**And that lab CANNOT be pre-committed the way `fstring_lab.py` was.**
`fstring_lab` was a NEW directory with no registered rows, so its
measured battery could land ahead of the implementation harmlessly.
`seq_lab` is not: it carries a checked-in extraction
(`seq_lab/seq_lab.json`) and a `seq_lab/spec.lean`. Writing `&` into
`seq_lab.py` before `ALLOWED_BINOPS` admits it desynchronises that JSON
and puts an unsupported node inside a lab whose OTHER rows are green —
breaking a triad on a file nobody asked to touch. The battery is
therefore specified here and written WITH the code, in one change, with
the extraction regenerated in the same commit.

In tier: `band(a, b)` over `(12, 10)`, `(255, 0)`, `(0b1011, 0b1101)`,
typed-bool pairs for all four boolness cells, `(True, 3)` and `(3, True)`
for the int-coercion cells, and the negative cells `(-1, 3)`, `(-5, 12)`,
`(12, -5)`, `(-4, -3)`, `(-3, -5)`, `(-100, 7)`, `(-1, -1)`;
`band_aug(n)` for the `&=` fold; `band_big()` for `((1<<100)-1) & 0xff`.
Faithful `TypeError`: `(1, "a")`, `("a", 1)`, `(1, None)`, `(1, [2])`,
`(1, (2,))` — the harness compares exception CLASS, and the message is
the existing fallback's, unchanged. Loud refusal: `&` with a set
operand, through the existing `.ref` arm. Same shape for `^` if the
rider lands. Plus `bor_neg` FLIPPED from `unsupported` to `match`, with
`(-1, 4)`, `(-1, -2)` and `(3, -1)` added, which is the visible proof
that the correction landed.

Not registered, deliberately: any `<<`/`>>` overflow row. Those belong
to the shift-budget work above, and registering one now as
`expect: unsupported` before the guard exists would be manufacturing a
green triad for a case that currently HANGS.

## The tail, construct 5: `Starred` DESIGNED — as THREE constructs, because the positions do not share a cost (2026-08-13)

### The design, stated before the argument for it

`Starred` is not one thing. `ast.Starred` appears in three positions with
three different prices, and the cheap one is free:

1. **Displays** (`[*a, 3]`, `(1, *a)`) — a LOWERING through `tuple(…)`.
   Zero AST constructors, zero walkers, **zero proof arms**.
2. **Assignment targets** (`x, *y = z`) — one `Stmt` constructor carrying
   NAMES, not a starred `Expr`. Three proof arms, the same three
   `assert` paid.
3. **Call sites** (`f(*a)`) — REFUSED, through a channel that already
   exists. Variadic arity dispatch is the real cost and it is unrelated
   to the other two.

Land 1 and 2. Refuse 3. `{**d}` and `f(**d)` are NOT in scope and not
`Starred` at all — measured: `{**d}` is `Dict(keys=[None], …)` and
`f(**d)` is `keyword(arg=None)`. Neither produces a `Starred` node.

### Where `Starred` actually occurs — measured, and the parse/compile line matters

The extractor runs `ast.parse`, and **`ast.parse` accepts starred
expressions that CPython refuses to COMPILE**. An instrument that checked
only `ast.parse` reported five of these as legal; re-run against
`compile(…, "exec")` they split (3.9.19, verbatim `msg`):

| source | `ast.parse` | `compile` |
| --- | --- | --- |
| `f(*a)`, `[*a]`, `x, *y = z`, `*y, = z`, `for *a, b in c: pass` | OK | OK |
| `*a` | OK | `can't use starred expression here` |
| `x = *a` | OK | `can't use starred expression here` |
| `x = *a,` | OK | **OK** (it is a tuple display) |
| `for *a in b: pass` | OK | `starred assignment target must be in a list or tuple` |
| `x, *y, *z = w` | OK | `multiple starred expressions in assignment` |
| `del *a` | `cannot delete starred` | (same) |

So the extractor MUST stay total over starred nodes in positions no
runnable program can contain. It already has the right vehicle:
`Expr.unsupported (pyKind) (text) (span)` — an EXISTING constructor. A
starred node in an uncompilable position ingests as
`Expr.unsupported "Starred" …` and costs nothing. This is the row that
would have been got wrong by checking parseability alone; it was, and it
is corrected here.

### Position 1 — displays LOWER, and the OBVIOUS lowering is the wrong one

`[*a, 3]` looks like `list(a) + [3]`. **It is not.** Measured in the
source, not assumed: `list(x)` **ALLOCATES A FRESH HEAP OBJECT**
(Semantics.lean:4286-4298, `allocListRun`), so it returns a `.ref`, and
`evalBinOp`'s `.ref` arm (Semantics.lean:521-527) refuses concatenation
of heap objects LOUDLY. The obvious lowering compiles to a refusal.

`tuple(…)` is the vehicle instead. It is the IMMEDIATE-value constructor
(Semantics.lean:4249-4285): `str`/`tuple`/namedtuple/`listV`/heap
list(snapshot)/`range`/generator(+`moduleGenFree` guard) all yield a
plain `.tuple`, and `+` on two immediate tuples is
`evalBinOp .add, .tuple, .tuple` (Semantics.lean:513). So:

* `(e1, *a, e2)`  ⟶  `(e1,) + tuple(a) + (e2,)`
* `[e1, *a, e2]`  ⟶  `list((e1,) + tuple(a) + (e2,))`
* `[*a]`          ⟶  `list(tuple(a))`

`list(…)` appears ONLY on the outside, where a fresh heap list is
exactly what CPython produces, and never as a concatenation operand.

**Evaluation order survives the lowering**, which is the thing a lowering
most easily breaks. `+` associates left, and `evalExpr`'s `binOp` arm
binds left then right, so `(e1,) + tuple(a) + (e2,)` evaluates `e1`,
then `a`, then `e2` — CPython's own left-to-right order. Measured
values: `[*[1,2], 3] → [1,2,3]`, `[*'ab'] → ['a','b']`,
`[*range(3)] → [0,1,2]`, `(*[1,2],) → (1,2)`, `[*[1,2], *[3]] →
[1,2,3]`, `[*[]] → []`. Each is what the lowering computes.

Inherited refusals, which is the reuse dividend: `[*d]` for a dict is
CPython's key iteration (`[*{'a':1}] → ['a']`) and `tuple()` over a dict
is already `.unsupported` on the order doctrine — loud, not wrong. Same
for a set receiver. A generator receiver already drains under the
existing `moduleGenFree` guard, which is exactly CPython's behaviour.

One honest mismatch, stated: `[*1]` is
`TypeError: Value after * must be an iterable, not int` in CPython,
while the lowering raises `'int' object is not iterable` from `tuple()`.
**Same exception CLASS, different message.** The harness compares
exception class names and never messages (the practice recorded at
Semantics.lean:1509-1510), so this passes — but it is a real divergence
and is written down rather than glossed.

**Set displays (`{*a}`) are OUT.** `{*[1,2]}` is `{1,2}`, and a set
result is loud in this tier on the order doctrine anyway; lowering it
would buy a value that almost every subsequent operation refuses.

### Position 2 — assignment targets, and the encoding question I got WRONG

The ranking said `Starred` "ALLOCATES … and reaches into the call
machinery; `worldInv` moves". Half right, and the half that is wrong
matters.

I assumed a `Stmt` encoding would be cheaper than an `Expr` encoding
because `Expr` is what the three mutual inductions induct over. **That
is false, and counting says so.** Taking the two most recent
constructors as the price list — `ifExp` (an `Expr`) and `assertStmt`
(a `Stmt`) — the arm sites are:

|  | Ast | Json | Semantics | Script | **Obs** | **ClockErase** | total |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `ifExp` (Expr) | 1 | 3 | 5 | 1 | **2** | **1** | 13 |
| `assertStmt` (Stmt) | 1 | 6 | 6 | 2 | **2** | **1** | 18 |

**Both cost exactly three proof arms** — `fuelMono` (Obs.lean:1071 for
`ifExp`), `worldInv` (Obs.lean:2410), `ceExecStmt_succ`
(ClockErase.lean:1393). The proof layer does not care whether the new
constructor is an expression or a statement; it cares only that there is
one. So the encoding must be chosen on OTHER grounds.

Chosen: **a `Stmt` constructor carrying names, no starred `Expr` at
all.**

```lean
| unpackAssign (before : Array String) (star : String)
    (after : Array String) (value : Expr) (span : Span)
```

The grounds are the ones the count cannot show. An `Expr.starred` would
have to be accepted by every expression walker and then REJECTED
everywhere except inside a target tuple — a constructor that is invalid
in almost all of its own positions, which is how the census holes get
made. `unpackAssign` is valid exactly where it can occur. It also keeps
the existing all-names restriction that `targetNames`
(Semantics.lean:2113-2117) already imposes on tuple targets, rather than
widening it: an attribute or subscript element beside a star is refused
by the extractor, as it effectively is today.

**The arity check reuses `unpackSeq`** (Semantics.lean:2222-2251), which
— like `evalBinOp` — sits OUTSIDE every `mutual` block (the neighbours
close at 1868 and open at 2623), so the proof layer meets it only
through `liftRes`. Its messages are ALREADY the measured CPython
strings: `too many values to unpack (expected {n})`,
`not enough values to unpack (expected {n}, got {size})`,
`cannot unpack non-iterable {typeName} object` — all three confirmed
verbatim against 3.9.19. The starred variant needs one sibling,
`unpackSeqStar`, differing in exactly two measured ways:

* the message is `not enough values to unpack (expected at least {k},
  got {m})` where `k = before.size + after.size` — measured:
  `a, *b = []` → `expected at least 1, got 0`;
  `a, *b, c = [1]` → `expected at least 2, got 1`;
  `*a, b, c = [1]` → `expected at least 2, got 1`.
* **there is no "too many values" case at all** — the star absorbs the
  surplus. `a, *b = [1,2,3]` binds `b = [2,3]`.

**The starred slice is ALWAYS a list**, whatever the source was —
measured: from a tuple `[2,3]`, from `'abc'` `['b','c']`, from
`range(4)` `[1,2,3]`, and `[]` when nothing is left. It is therefore an
ALLOCATION, and it should be a HEAP list, not a `.listV`, for
consistency with `list()` and with `[…]` displays (both allocate) and
because `y.append(…)` must work on it.

**What that does to the fragment — and it is NOT "worldInv moves".**
Because the statement allocates, `Stmt.heapFree` returns `false` for it,
exactly as it already does for `| .subscript ..` and `| .attribute ..`
targets (Semantics.lean:3397-3403). A statement outside the fragment
makes `worldInv`'s obligation VACUOUS. So the allocation costs COVERAGE,
not proof: `worldInv` gains an arm that is discharged the way the other
non-fragment arms are, and no fragment reasoning has to be redone. The
ranking's instinct ("it allocates") was right; its conclusion ("worldInv
moves") overstated the consequence.

**Order, and the all-or-nothing property.** The iterable is fully
drained BEFORE any target binds — measured with a generator that yields
twice and then raises: both yields ran, the exception propagated, and
`a` was NOT bound. So there is no partial-binding state to model, which
is what keeps this a single `liftRes` over a pure function rather than a
threaded store.

`for a, *b in …` and `[(a,b) for a, *b in …]` both work in CPython
(measured) and are OUT of this design: they need the same slice logic at
a different binding site, and adding them later is additive.

### Position 3 — call sites are REFUSED, and the channel already exists

`Expr.call` already carries `callUnsupported : Option String`, whose own
doc comment says "`**` unpacking and starred args ride in
`callUnsupported` (loud)" (Ast.lean:87-93). Admitting `f(*a)` means
variadic arity dispatch against a callee whose parameter list is only
known at runtime, and the measured error surface is worse than that:

    foo(*1)  →  TypeError: __main__.foo() argument after * must be an
                iterable, not int

The message embeds the callee's MODULE-QUALIFIED name (`__main__.foo`,
and `__main__.show.<locals>.<lambda>` for a lambda) — a qualname the
model does not track. Contrast the display form, `[*1] → Value after *
must be an iterable, not int`, which carries no name at all. That
asymmetry is a second, independent reason the displays land and the call
sites do not.

Arity errors are the callee's own and already faithful when the call is
spelled out: measured `two(*[1])` →
`missing 1 required positional argument: 'y'`, `two(*[1,2,3])` →
`takes 2 positional arguments but 3 were given`.

### Surface added

**Position 1: extractor only.** The lowering lives beside the f-strings
lowering in `extractors/python/extract.py`, in the `ast.List`/`ast.Tuple`
clauses. Zero Lean surface, zero walkers, zero proof arms.

**Position 2:** one `Stmt` constructor (`unpackAssign`) and its doc
comment; one `unpackSeqStar` beside `unpackSeq`; one `execStmt` arm; one
`Json.lean` ingestion arm; the same walker set `assert` touched, plus
the two G1 target walkers that already special-case tuple targets
(`Expr.g1TargetStoresList` at Semantics.lean:2790, `targetBindsListG` at
2814 — `g1Binds` is `before ++ [star] ++ after`, which is EXACTLY known
here, unlike `del`'s conservative `true`); three proof arms
(Obs.lean x2, ClockErase.lean x1), each in the non-fragment shape.

**Position 3:** one extractor clause populating `callUnsupported`. It
may already be populated — to be MEASURED at implementation time, not
assumed, since `ALLOWED_BINOPS`-style gates have been found missing
before.

Open at implementation time, to be MEASURED not assumed: whether
`Stmt.g1Dirty` can be `false` for `unpackAssign` (its binds are known
exactly, so it should be, but the walkers must be total first).

### Battery to build (rows measured above; registered WITH the code)

A NEW `Examples/python/star_lab`, not an extension of an existing lab —
the `seq_lab` hazard recorded under construct 4 applies here too, and a
new directory with no registered rows is the only shape that can be
measured ahead of the implementation.

In tier, displays: `[*a, 3]`, `[1, *a]`, `[*a, *b]`, `[*a]`, `(*a,)`,
`(1, *a)`, over a list, a tuple, a `str` and a `range` receiver, plus
the empty receiver `[*[]] → []`. In tier, targets: `x, *y = [1,2,3]`,
`x, *y = [1]` (slice `[]`), `*y, x = [1,2,3]`, `a, *b, c = [1,2,3]`,
`a, *b, c = [1,2]` (slice `[]`), `x, *y = (1,2)`, `x, *y = 'abc'`,
`x, *y = range(3)`, and `*y, = [1,2]`.

Faithful exceptions: `x, *y = []` → `ValueError`, `a, *b, c = [1]` →
`ValueError`, `x, *y = 5` and `a, *b = None` → `TypeError`. Loud
refusals: `f(*a)` at a call site, `{*a}` as a set display, `[*d]` for a
dict receiver, and a starred `for`-target. Plus a script whose stdout is
compared byte-for-byte.

Not registered, deliberately: the uncompilable positions (`*a`,
`x = *a`, `x, *y, *z = w`, `for *a in b`). CPython cannot RUN them, so
there is no oracle output to compare against; they belong in an
extractor totality test, not in `cases.json`.

## C intrinsics — proposal written, OWNER-GATED (2026-08-14)

The import-ceiling census's follow-up decision — whether to model C
extension modules as Lean intrinsics — now has its design memo:
[docs/c-intrinsics-proposal.md](c-intrinsics-proposal.md). Ranked
targets recomputed from the census JSON's strict closures (greedy
cover: `sys` 7, `+_weakref` 12, `+posix` 22 import-clean — but the
SWEEP movers are `_contextvars` and `_struct`, one flip each, name-only
opaque intrinsics with zero modeled semantics); the intrinsic contract
(pinned inventory, per-NAME member tiers CONSTANT/FUNCTION/STATEFUL/
OPAQUE, the loudness rule, the accelerator-equivalence obligation);
cost shape per candidate from consumer usage, not module API; and the
recommendation (pass 0 = the guarded import forms alone, buying
`bisect`; pass 1 = `_contextvars` + `_struct`; pass 2 = a `sys`
constant slice), with the honest total of **+3 to +4 files of 154**
and the three separable owner questions stated at the end.

**GATED: nothing in it may be built until the owner answers.** The
proposal is a memo, not a plan of record; a "no" on any of its three
questions drops the corresponding pass and the ceiling stands at
4/154 as measured.

## Import forms (Pass 0) — DESIGNED, rides the next rebuild (2026-08-14)

Design recorded: docs/memory-model.md §import forms (Pass 0).

**IMPLEMENTATION AUTHORED (branch `pass0-impl`, 2026-08-14) — compiles
at the shared rebuild window.** The five-commit series lands the whole
design: (1) the extractor arm + the pinned platform inventory
(`extractors/python/platform_inventory.json`, 309 modules, 3.9.19,
captured by `capture_inventory.py`) + 16 unit rows — the ONLY runnable
verification today, 55/55 green under python3; (2) `Stmt.importFrom` +
ingestion with the default-tolerant `star` and the benign-whitelist
canonicalization (one rewrite site, five text-keyed consumers see
unchanged shapes — as-built note in the design section records the
extractor's benign-text third disjunct that makes the envelope claim
true); (3) `PyErr.importError`, `errName`/`errMessage`'s exact
`ModuleNotFoundError` surface, `importErrorHandlerMatch` (the pinned
two-name table) at execStmt's tryStmt arm, the census arms
(g1Binds/g1Stores/g1ExecCandidate/heapFree/genAllocFree/kindName), and
the three inductions threaded arm-for-arm on their neighbours
(fuelMono/worldInv/clockErase — importFrom is a fuel-free raise leaf;
the tryStmt findClass-none branch gains the table's ite with the class
branch's body/handler IH shape, no cid ite); (4) the Script.lean try
shell (second table site, per-statement publish) + the recorded
scriptImports view decision + the survey verified unchanged by
construction on a fresh probe envelope; (5) the battery — import_lab
(happy_fallback / rebind_after_fallback / guarded star) and five
scripts, oracle side measured against the pinned 3.9.19 NOW, six
scripts.json rows note-tagged REBUILD-WINDOW.

**Rebuild-window verification list** (nothing below is claimable
today): `lake build` (~60 min full cycle); the six scripts.json rows
(`import_not_top_level` and `import_insort_fallback` expect
UNSUPPORTED — insort's memo-2.5 obligation stands OPEN on
`list.insert`, flip to match when it lands; a `import_bisect_fallback`
divergence is a BLOCKER); survey headline re-measured (predicted 161
REFUSE, flip set exactly {bisect} — anything else is a finding);
`import`-wall population re-measured (predicted to DROP from 154, not
predicted by how much); envelope re-extraction + `pins_common.lean`
only (the JSON-content trap — sunfish's two benign from-imports
structure in the envelope and canonicalize back at ingestion); exc_lab
unchanged (no row pinned the old refusal text); corpus/script sweeps
re-counted in the same triad. If the owner answers NO on memo question
2, drop the guard disjunct in extract.py's ImportFrom arm before
building — the absent-module machinery and the handler table still
land, bisect does not flip.

**LANDED (master, 2026-08-14, the shared rebuild) — the list above,
MEASURED.** One rebuild carried f-strings + BitAnd + Pass 0, in the
composed order (extractor first, every envelope re-extracted,
`pins_common.lean` only per the JSON-content trap, one build, both
batteries in the same triad). `lake build` green twice — the full
pass 3658 jobs with ZERO errors (the never-compiled series built
first try) and the incremental pass against the re-extracted
envelopes. Triad: docs_check 67/67; extractor units 55/55;
diff_test 1102 cases 0 failed — after the differential CAUGHT the
BitAnd battery's two mal-encoded container-arg rows (nested
list/tuple elements must be canonical typed values; the bare-number
convenience is top-level-only) — script_corpus 42 scripts, 35
matched, 7 loud-blocked, all expected. Surveys (oracle CPython
3.9.25, pinned family; seed census 166 — the laptop pin's 167th
seed `sitecustomize.py` is a Homebrew artifact, not stdlib): in-repo
86 MATCH / 18 REFUSE / 0 DIVERGE; wild sweep 6 MATCH / 160 REFUSE /
0 DIVERGE — the census-adjusted predicted count exactly, but the
flip IDENTITY is the finding the pre-registration existed to catch:
**bisect did NOT flip** — behind its import wall sits
`bisect = bisect_right` / `insort = insort_right`, a function
referenced as a VALUE, outside the tier; that is bisect's mapped
next wall (the §2.5 fallback-equivalence rows themselves pass, so
the guarded-arm admission stands). **stat DID flip** REFUSE→MATCH:
its last wall was BitAnd, landed in the same rebuild — the tail's
"+1 now" delivered by a different file than predicted.
quopri/opcode stand on `del`/bytes as designed. PENDING: the laptop
working tree's uncommitted f-strings edits are fully contained in
this landing (verified line-for-line) — reconciling that tree is a
separate reviewed step, not this record.

Original design summary follows. The paying surface is the census's own: absolute `from X import
names`/`*` at module top level, a missing module raising a CATCHABLE
`ImportError` — new `PyErr.importError`, boundary-rendered as CPython
3.9's `ModuleNotFoundError: No module named '…'`, and the exceptions
tier's recorded first extension (builtin-name handler matching) landing
at minimum width: a pinned two-name table for that one kind. The
importable universe stays EMPTY: platform-absent modules raise
faithfully anywhere; platform-present unmodeled ones (`_bisect`,
`binascii`, `_stat`, `_opcode`) are admitted by the EXTRACTOR only in
guarded `try`/`except ImportError:` position, under the memo's §2.5
accelerator-equivalence obligation — that arm alone consumes owner
question 2 and is dropped, not widened, on a "no". Today's refusal site
is no site at all — imports fall through `convert_stmt` to the generic
`Unsupported` channel; the narrowing structures only the paying shape,
so the survey's wall census is correct unchanged. Stated invariant: no
import form is bind-invisible (star is unanalysable by fiat), so
`moduleClockOk` and the namedtuple census refuse conservatively and a
from-import can never route around the trace-clock discipline.
Measured claim: `bisect` flips on this alone; `quopri`/`stat`/`opcode`
wait for `del`/`BitAnd`/bytes; nothing else moves. Rides the SAME full
rebuild as the HELD f-strings tail (extractor first, envelopes
re-extracted, `pins_common.lean` only, both batteries in one triad).

## Module-level def aliasing — DESIGNED (2026-08-14)

Design recorded: docs/memory-model.md §module-level def aliasing.
bisect's mapped next wall (`bisect = bisect_right`, a def referenced
as a VALUE) narrows to the one admissible shape: a module-level alias
of a top-level def, never rebound. Mechanism is PURE INGESTION — a
second `Module.functions` entry (the target defn copied under the
alias name, span := the alias statement), the assign rewritten to
`pass`; the alias never exists as a runtime value, so no theorem
moves and the interpreter is untouched. `defsBoundBefore` (ordering)
and `initBindable` (rebind refusal) extend to alias names for free
because both key on `Module.functions`. One relocation:
`isBuiltinName`/`isPyBuiltinName` move verbatim Semantics.lean →
Ast.lean so the ingestion census can consult them. Census: analyzable
top level (structured `importFrom` binds nothing — Pass 0 raises
before binding; §2.5 carries the guarded-accelerator divergence), no
`has_global` anywhere, target = earlier top-level def or admitted
alias (transitive, source-ordered, end-before-line), target and alias
bound by no other top-level statement, alias a plain non-dunder
non-builtin non-definition identifier. Rebind-after-alias REFUSED
(admission + `initBindable` backstop), never executed through.
Measured prediction (box survey, 3504397): flip set exactly {bisect}
— 6→7 MATCH / 160→159 REFUSE; ten seeds contain the pattern, nine
behind earlier walls (operator.py alone holds 47 alias statements —
value parked behind its class-creation wall). `insort` consumers
still wait on `list.insert` (§2.5 residue). Battery: alias_lab
(alias≡direct incl. kwargs + generator rows, alias-of-alias, chain)
plus four scripts (happy / before-def REFUSE / rebound REFUSE /
bisect-shape MATCH). Lean-only change ⇒ no envelope re-extraction;
rides a box rebuild with the standard triad + both surveys.

**LANDED (master, 2026-08-14, box-verified) — the design above,
MEASURED.** Box build green (3659 jobs, EXIT=0) after ONE fix the
battery itself caught on the first box run: `splitChains` gives every
piece of `chain1 = chain2 = f` the SAME span, so the strict
end-before-line ordering test wrongly rejected `chain2 = chain1` — the
`#py_check chain2(9) = 18` was the only red target of 3659; an
admitted-alias target is now ordered by the FOLD (CPython's
left-to-right chain order), a def target keeps the span test.
Verification (box, oracle CPython 3.9.25, pinned family, stamped):
extractor units 55/55; diff_test 1121 cases / 0 failed / 89
whitelisted (the 19 new alias rows all match — alias≡direct oracled by
name); script_corpus 46 scripts / 0 failed / 37 matched / 9
loud-blocked (+2 matched: alias_script, alias_bisect_shape; +2 loud as
designed: alias_before_def, alias_rebound); in-repo survey 89 MATCH /
20 REFUSE / 0 DIVERGE (from 86/18 — the three new positive files
match, the two refusal scripts refuse); **stdlib sweep 7 MATCH / 159
REFUSE / 0 DIVERGE — bisect.py REFUSE→MATCH (exit 0, 4 live
statements), the pre-registered flip set exactly {bisect}, nothing
else moved.** Tripwire: cotenant gauntlet 0 forfeits across all three
builds and every harness run. The honest chain stands as designed:
`insort` CONSUMERS still refuse on `list.insert`
(`import_insort_fallback` stays UNSUPPORTED — the §2.5 residue, next
tier when it lands).

## `list.insert` — the §2.5 residue — DESIGNED (2026-08-14)

Design recorded: docs/memory-model.md §`list.insert` (the §2.5
residue). The one method blocking the insort-fallback CONSUMERS.
CPython 3.9 semantics measured: the index CLAMPS (negative from the
end, floored at 0; beyond-end appends — never IndexError), `None`
returned, in-place through every alias; faithful `TypeError`s verbatim
(non-int index after argument evaluation; `insert expected 2
arguments, got {n}`). Mechanism is append's frame exactly:
`AttrPlan.listInsert` + the `attrCallPlan` list arm + one
`execAttrCall` arm + the loud kwargs arm; worker `heapInsert` beside
`heapAppend`/`heapPop` (take/drop form — core `List.insertIdx` DROPS
out-of-range, the opposite of the clamp), joining the append/pop simp
sets. seqBudget: NO interaction, stated as a rule — the budget guards
single-step materialization, per-call growth-by-one is fuel-bounded
(append's discipline), so no budget-exceeded battery row exists (N/A
by design). Theorems: no new mutual member; fuelMono one arm
(listAppend's shape), worldInv ZERO arms (`attr = "get"` pin; one
`if_neg` in `attrCallPlan_get_heapFree`'s list case), clockErase one
real arm (listPop's asInt geometry at two args) + three enumerated
`.unsupported` lines. Extractor/envelopes UNTOUCHED (dynamic refusal
today) — no re-extraction. Pre-registered flips:
`import_insort_fallback` UNSUPPORTED→MATCH outright (the memo-2.5
insort discharge); in-repo existing-file flip set exactly that row
(89→90 MATCH / 20→19 REFUSE + 1 new script → 91/19); **stdlib sweep
NO change (7/159) — consumer-level only**; anything else is a finding.
Battery: list_lab clamping grid / empty / alias / returns-None /
verbatim insort_right / two TypeError rows, plus NEW
`insort_alias_script.py` (alias tier composed with insert).

**LANDED (master, 2026-08-14, box-verified) — the design above,
MEASURED, every pre-registered number exact.** Box build green FIRST
TRY (3659 jobs, EXIT=0 — no battery-caught fix needed this time; the
sunfish poles pins_bound/pins_clock ~23 min each). Verification (box,
oracle CPython 3.9.25, pinned family, stamped): extractor units 55/55;
docs_check 67/67; diff_test 1141 cases / 0 failed / 89 whitelisted
(the 20 new insert rows all match — clamping grid, empty, alias,
None, both TypeErrors by message, insort_right verbatim);
script_corpus 47 scripts / 0 failed / 39 matched / 8 loud —
**`import_insort_fallback` UNSUPPORTED→MATCH, the memo-2.5 insort
obligation DISCHARGED** (pure fallback vs the C accelerator, same
list, exception class compared), plus `insort_alias_script` MATCH
(alias tier composed with insert); in-repo survey 91 MATCH / 19
REFUSE / 0 DIVERGE (predicted 91/19: the one flip + the one new
script); **stdlib sweep 7 MATCH / 159 REFUSE / 0 DIVERGE — UNCHANGED,
as pre-registered: consumer-level only, no stdlib file had `.insert`
as its sole wall.** Theorem cost as designed: fuelMono one arm,
worldInv zero arms (one `if_neg` in `attrCallPlan_get_heapFree`),
clockErase one real arm + three enumerated refusals; no new mutual
member. Tripwire: the live queue match ran 231→335 games during the
build, 0 forfeits, 0 illegal. One process note: the first
verification pass launched harness jobs without `~/.elan/bin` on the
non-interactive PATH, so diff_test/script_corpus died on `lake` —
rerun with the PATH exported; the numbers above are the rerun's.
