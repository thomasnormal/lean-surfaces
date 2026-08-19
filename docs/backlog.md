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
`while … else` was the only compound still delegated wholesale; it got
its shell on 2026-08-15 (`execScriptWhile` gained the `orelse` block —
taken on exhaustion, skipped by `break`, `execWhile`'s covenant verbatim;
all three exits pinned in `harness/scripts/while_else_script.py`), so no
compound the executor RUNS is delegated now. `scriptFlushCoherent` stays
as the standing tripwire that would catch the next missing shell — its
only remaining contributors are the `for … else` shapes the executor
refuses outright. The refusal left both sweeps.

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

   **CENSUSED AND STOPPED (2026-08-15) — the estimate above is WRONG, and
   this is the record of why.** The flip was authored (the wrapper edit
   below is real and was reverted, not lost) and then stopped at the
   blast-radius census, BEFORE a build, because the census says this is
   not a wire-in plus five rebases. Two measured facts:

   * **The rescue lemma covers ONE of the five.** Of the five example
     proofs only `sf_bound_for` iterates its list argument with `for`;
     `execForList_eq_execFor_snapshot` is exactly its obstacle and
     exactly nobody else's. `sf_bound_rec` and `bench_bisect` SUBSCRIPT
     the argument (`indexVal` → `indexValH` through a ref, `while`
     loops), `bench_statistics` runs it through `sorted` (`sortedVal` →
     the ALLOCATING `sortedValH`), and `sf_bound_tree`'s argument is a
     `Val.tuple` CONTAINING a `Val.list` (`GTree.toVal`), so the thaw
     allocates inside a tuple. None of those four has built machinery.
   * **The break is in the MARSHALLING NORMAL FORM, below the loops.**
     `Surface.lean`'s `@[simp] thaw_toVal_list` normalizes a marshalled
     list argument to `RVal.listV (…)` — the immediate form the flip
     removes — and `asIntList_map_toVal`/`asIntList_map_thaw_comp` (the
     bridge `bench_statistics` runs entirely through) are stated over
     that same element shape. After the flip a list argument is `.ref a`
     with the heap grown, so these three lemmas stop describing what the
     boundary produces and no heap-side twin exists. Downstream of that:
     `sf_bound_for`'s pinned world `pw := ⟨#[], …⟩` is EMPTY-heaped and
     its loop environment binds `("scores", RVal.listV …)`; both are
     restatements, not rewrites, and the same is true of
     `bench_bisect`'s three loop environments and the `arrVal_getElem` /
     `arrVal_getD` subscript helpers.

     CORRECTION (2026-08-15, after `d19b0e2` landed the same day): that
     last family is no longer example-local — the promotion moved
     `arrVal_getElem`/`arrVal_getD` (and `map_getElem?_getD`, the
     `getD`/`getElem` bridge) into VCTactic.lean §marshalled-list
     indexing, with only `bench_statistics` keeping a one-line local
     instance over the shared proof. That makes stage 1 CHEAPER than
     priced: the marshalled-list indexing shape now needs ONE heap-side
     twin in the shared file rather than three example-local ones. The
     rest of the census is unaffected — the promoted lemmas are stated
     over the immediate `RVal.listV` marshalling, so they still describe
     the pre-flip boundary and still need that twin.

   PRICED, in landable stages (each its own build; stage 1 is the only
   one with no user-visible change):

   1. **Heap-side marshalling normal form** — `thaw_toVal_list`'s
      ref-shaped twin, `asIntList` at a heap list, `indexValH` and
      `sortedValH` subscript/sort helpers at a `ToVal`-marshalled
      argument. Pure addition, nothing flips, everything still builds.
      This is the missing ENGINE, and the honest analogue of what
      `execForList_eq_execFor_snapshot` did for the `for` case.
   2. **The wrapper edit** — DECIDED SHAPE, authored 2026-08-15 and
      recorded here so it is not re-derived: a named
      `boundaryEntry (w : World) (args : Array Val) : World × Array RVal`
      = `thawArgsH` on `w.heap` re-seated into `w`, shared by
      `callFunction` and `callFunctionClock` (both keep their
      signatures), plus `boundaryEntry_of_listFree` (on list-free
      arguments it is `(w, RVal.thawArgs args)` — the bridge every
      pre-flip statement rides) and `boundaryEntry_clock` (the entry
      touches only the heap). `thawH`/`thawListH`/`thawArgsH` and
      `boundaryEntry` join `py_simp` and `interpUnfolds`.
   3. **The `Val.listFreeArgs` autoparam sweep** — the census's real
      cost. Every lemma whose STATEMENT pins the public geometry at
      `initWorld m` with `RVal.thawArgs args` needs the argument-side
      guard its return-side twin already has (`Val.listFree v`):
      `Surface.lean`'s `CallsTo.callsIn_frame` / `callIn_at_least`;
      `VCTactic.lean`'s four `PyTriple.exists_callsTo*` bridges;
      `VC2.lean`'s `callsTo_arityOk` / `toTriple` / `callsTo_iff_triple`
      / `raises_*` family; `Obs.lean`'s `callFunction_mono`;
      `ClockErase.lean`'s `callFunctionClock_nil`/`_ok`/`_exn`/
      `_timeout`; `LoopTactic.lean`'s `py_begin` entry normal form;
      `VCTests.lean`'s entry shape. Autoparams keep every existing
      call site unchanged — list-free arguments are the norm — so this
      stage is mechanical but wide.
   4. **The five rebases**, in ascending cost: `sf_bound_rec`
      (subscript only), `bench_statistics` (stage-1 lemmas), then
      `sf_bound_for` (the rescue lemma applies once the world and
      environment are restated), `sf_bound_tree` (nested thaw), and
      `bench_bisect` last (947 lines, ~400 of them one block).
   5. **The payoff**, which is real and should be stated: two harness
      rows go from REFUSE to MATCH — `sf_hist.push` and
      `sf_hist.rotate_scores`, today `"expect": "unsupported"` in
      `harness/cases.json`, are the arg-mutation rows the whole flip
      exists for. `Surface.lean`'s `py_prove_residual_guard` root list
      must gain `execForList` in the same landing (it has `execFor` and
      not the cursor, so a residual live-cursor goal would slip the
      guard).

   Nothing in the census contradicts the DESIGN — the flip is still the
   right next step and `boundaryEntry` is still its shape. What the
   census contradicts is the SIZE: stage 1 is a missing engine, not a
   detail, and stages 3-4 are the bulk. Do not start this behind a
   single-session budget.

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
   `ord`/`chr` (parse/render), `sorted()` on strs. **The attribute-call
   heapFree whitelist is DONE (2026-08-15)** — it is no longer
   `.get`-only. `heapFreeAttr` names the six admitted attributes
   (`get` plus the pure str set, which had grown from the trio recorded
   here to `swapcase`/`isupper`/`islower`/`upper`/`index`);
   `attrCallPlan_get_heapFree` generalized to `attrCallPlan_heapFree`
   (the mutating arms die on `heapFreeAttr_ne` instead of on literal
   comparisons, so the proof never needs to know WHICH name it has), the
   `worldInv` attribute case lost its `attr = "get"` subst, and its str
   receiver arm — previously vacuous, since `strCallPlan "get"` refuses
   — carries the five pure plans explicitly. `time` is deliberately
   OUT (a clock read consumes a reading:
   `isClockCall_of_heapFreeAttr`), as are `.clear` and the list
   mutators. Proof-side only: no interpreter behaviour changes and no
   differential verdict moves; what it buys is that a function calling
   a pure str method can now be IN the world-preservation fragment.
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
  row. ~~Passing it is the standing OWNER-GATED abstraction decision
  (memory-model §wall-clock time)~~ **CORRECTED (2026-08-15) — NOT
  gated, and not since the day after this was written.** §Pass 6
  immediately below opens "The 2048-node wall's owner-gated decision is
  DECIDED: time as an INPUT, not an effect", the trace clock was BUILT
  the same day, and §Pass 7 landed CLOCK ERASURE on top of it. This
  line survived as the only place still advertising a gate that no
  longer exists — read §Pass 6 and §Pass 7 for the decision as taken.
* **The eviction `del`s** (bound(): `del self.tp_move[next(…)]`,
  `del self.tp_score[next(iter(…))]`) ingest as
  `Stmt.unsupported "Delete"` and are dynamically DEAD below
  TABLE_SIZE — no search-stepping depth reachable under the node wall
  ever executes them. They gate nothing until the wall falls.
* **main()/UCI** stays the leanpy-shell surface (far beyond one
  milestone); ~~`input` is still absent from `isBuiltinName` (recorded
  pass-4 gap — add loud with the next builtin sweep, it rides any
  future Semantics.lean rebuild rather than paying the 80-min pole
  alone)~~ **CORRECTED (2026-08-15): `input` IS in `isBuiltinName`** —
  `Ast.lean:517`, where the pair moved verbatim from Semantics.lean on
  2026-08-14 (§module-level def aliasing). The pass-4 gap closed on some
  later builtin sweep exactly as predicted and nobody struck the line.

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
   traces (the batteries' trust level). ~~OPEN: a kernel-affordable
   concrete-run route (kernel-reducibility work on `initWorld`'s hot
   path is the natural candidate) would upgrade the headline rows to
   unconditional `∀ tr` theorems by one application each.~~ **CLOSED
   (2026-08-15, by §Pass 8 milestone 1 below):** "Milestone 1 also
   closes the KERNEL-AFFORDABILITY item DEFINITIVELY" — kernel
   reduction measured at ~1000× native per interpreter step, so
   search-scale `∀ tr` theorems stay transport + native-`#guard`
   paired unless the interpreter is re-engineered for kernel
   reduction. Recorded there, not scheduled; not an open item.
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
bearing modules never enter the fragment); ~~the leanpy script-mode
trace flag (pass-6 deferral — small)~~ **CLOSED (2026-08-15): it
shipped** — `tools/leanpy --clock i,j,k`, recorded at the top of this
file ("this CLOSES the pass-6 script-mode trace-flag deferral —
`runScript` is now `runScriptClock m []`"); deeper stepping beyond
depth 4 (more readings, same machinery — cost-gated, not
construct-gated).

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

### LANDED (master, 2026-08-14, the box cycle) — measured vs pre-registered: EXACT

Build 3659 jobs, ZERO errors, after two proof-arm corrections the
never-compiled series needed: (1) a doc comment must be IMMEDIATELY
followed by its declaration — the new ingestion defs had been inserted
between `recognizeDefAliases`'s docstring and its `def` (parse error at
the next `/--`); (2) `ClockErasedF.ok`'s implicit `{st}` must be given
EXPLICITLY (`(st := { st with locals := env })`, `RFlow.next` spelled
out — `v` is polymorphic): passing `h` first pins the state to the
UN-updated frame, defeq at `.world.clock` but not at the ok-state — the
H3 eager-unification trap in a new costume. Obs.lean's two arms and the
function-scope arm compiled first try at the recorded pricing.

Verification (box, oracle CPython 3.9.25 stamped on every instrument):
diff_test **1159 cases, 0 failed** (1062 matched, 97 whitelisted — the
twelve del_lab rows land as registered, the three census over-refusals
pinned); script_corpus **55 scripts, 0 failed, 44 matched, 11
loud-blocked** (the 8 del scripts: 5 MATCH including the opcode-shaped
trailing pin, the mid-statement `if`-shell removal, and the partial
`del f, x, nosuch` NameError; 3 loud: non-trailing def-del, dunder,
import-name); extractor units 65/65; docs_check 67/67; in-repo survey
**119 files — MATCH=97, REFUSE=22, 0 DIVERGE** (from 89 MATCH at the
insert landing; the del battery files all count); stdlib sweep
**166 files — MATCH=7, REFUSE=159, 0 DIVERGE, flip set EMPTY** (the
same seven: bisect, stat, sunau, chunk, nturl2path, `__phello__.foo`,
`_sysconfigdata…`).

**The pre-registered prediction held exactly**: opcode.py did NOT flip,
and its refusal message MOVED off `unsupported statement 'Delete'` onto
`'%' string formatting is outside the v0 tier` (measured directly:
`tools/leanpy /usr/lib64/python3.9/opcode.py` on the box) — the
acceptance signal that `del` itself cleared. opcode's honest chain is
now del (LANDED) + a `%`-formatting slice (`str % (int,)` under
`%r`/`%d`, buildable on the shipped `reprVal`) — the measured
next-construct candidate, deliberately not built here. The stdlib's
static Delete census drops to the non-bare forms (142 nodes in 56
files, all subscript/attribute/starred — clause 4's boundary, intact).

Tripwire: the live gauntlet (`elo-null-r4-d7-em100-20260814`) ran
208 → 358 games during the cycle with 0 forfeits; every other arena
unchanged, 0 forfeits everywhere. Instrument note: leanpy's
binary-freshness WARNING is an mtime heuristic and fires falsely after
a `git reset` (lake replays by content hash — 16/16 replayed, nothing
rebuilt); the del rows themselves are the witness that the binary
carries the semantics.

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
taken with `>>`, not smuggled in with `&`. ~~**Recorded as a live defect
in shipped `<<`, not as a new one.**~~ **CLOSED for `<<` (2026-08-15,
§the `<<` budget below)** — `shiftBudget` landed, and the measured
failure was an `INTERNAL PANIC`, not the hang predicted here. `>>` is
unaffected because it was never admitted: `RShift` is in neither
`ALLOWED_BINOPS` nor the `BinOp` inductive, so it still refuses at
extraction and inherits the budget free if it is ever added.

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

### STATUS: position 1 is BUILT (2026-08-13, docs/memory-model.md §starred displays)

The DISPLAY lowering landed exactly as designed above — extractor-only,
so `lake build` was a pure replay plus the two new example specs (3660
jobs, from 3658). Positions 2 and 3 stay refused and are now pinned by
row, not assumed.

TWO CORRECTIONS the implementation MEASURED, both of which the design
predicted the other way:

* **Position 2 did not refuse — it answered a FAKE `ValueError`.** The
  design said the existing all-names restriction in `targetNames` already
  refuses a starred target. It does not: `unpackSeq` checks ARITY BEFORE
  element kinds, so `x, *y = [1, 2, 3]` answered
  `too many values to unpack (expected 2)` where CPython binds
  `y = [2, 3]`. A wrong answer, not a loud one. The whole target now
  ingests as `Unsupported "Starred:target"`. This is a pre-existing
  defect, found only because the position was pinned by a row.
* **The lowering needs a SHADOW CENSUS the design did not name.** It
  spells the display as calls of the names `list` and `tuple`; a module
  binding either would run the display through the shadow while CPython's
  display looks nothing up. `Examples/python/star_shadow` is the row that
  catches the census being dropped — the same shape the f-string
  lowering's `str` census has, and it should be read as a rule for
  lowerings generally: a lowering that synthesizes a NAME owes a census.

Position 3 needed nothing: `callUnsupported` already carried
`starred args`, measured rather than assumed, as the design asked.

### REBASED onto master (2026-08-16) — and the sweep delta is ZERO FILES

The branch sat 58 commits and spanned an envelope re-extraction. Rebased,
re-extracted, gated, and the honest headline is that **the display
lowering moves no file on either wild corpus.**

Mechanically it was small: one cherry-pick, two conflicts (`backlog.md`
and `scripts.json`, both tail-of-file), `extract.py`/`memory-model.md`/
`cases.json` auto-merged. Every `#py_check` in `star_lab/spec.lean`
passes against the FRESHLY re-extracted envelope, which is the real
verification that the lowering still computes the right answers 58
commits later — 3660 → **3662 jobs, green**.

**THE SWEEP DELTA, all four:**

| instrument | before | after |
| --- | --- | --- |
| stdlib sweep | 6 MATCH / 161 REFUSE | **6 / 161, MATCH set IDENTICAL** |
| library baseline (197) | 12/7/41/136/0/1 | **byte-identical — every module verdict AND all 3448 call verdicts** |
| in-repo survey | 102 MATCH / 25 REFUSE of 127 | 105 / 25 of **130** — the three new battery files, all MATCH |
| script corpus | 63 scripts, 49 matched | 64, 50 matched, 0 failed |
| diff_test | 1236 cases | **1271**, 0 failed |

The static census is where the lowering shows at all, and it shows
SMALL: stdlib `Starred` nodes **190 → 183**, still present in 68 files,
sole-blocker 0. Seven nodes. The reason is the design's own
three-position split: the stdlib's starred nodes are overwhelmingly CALL
ARGUMENTS and ASSIGNMENT TARGETS, and the display is the rare one. §THE
SEQUENCING PRINCIPLE predicted the shape ("`Starred` looks like 86 and is
worth 3") and this is the sharper version of it — worth 3 files was the
whole construct; position 1 alone is worth zero.

**TWO CORRECTIONS the rebase measured** (docs/memory-model.md §starred
displays, "AS REBASED"):

1. **Position 2's defect was fixed TWICE, independently.** Master closed
   it from the STATEMENT side on 2026-08-15 while this branch held the
   EXPRESSION side. Both are kept, because master's covers `ast.Assign`
   and nothing else — a `for`, `with … as`, or comprehension target
   reaches only the expression arm. Master's is the stronger one for an
   assignment, and it is the shape `star_lab.json` now re-extracts to.
2. **The `for` target was ALREADY loud, and the obvious inference is
   false.** Probed at all three arities that separated wrong answers from
   loud ones in the `Assign` case: master REFUSES all three
   (`unpacking targets other than plain names`), because `execFor`'s
   target check is name-only and fires BEFORE arity — exactly where
   `unpackSeq` differed. So this arm is a MESSAGE change for `for`, not a
   soundness fix. Only the probe says so.

**ONE DEDUP the second lowering exposed:** `binds_str` was
`binds_any_name` with `names = {"str"}` inlined, line for line. One
census function now, two named name sets, both decided in one place.
Behaviour-neutral: 74/74 extractor units, and re-extracting every tracked
envelope moved nothing but the `frontend.version` stamp.

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

## `%`-formatting — opcode.py's sole wall — DESIGNED (2026-08-14)

Design recorded: docs/memory-model.md §`%`-formatting on strings. The
`del` landing named the chain and this is its last link.

**The price, measured first.** Master's stdlib sweep dynamic telemetry
ranks `'%' string formatting is outside the v0 tier` as the sole wall of
exactly ONE file of 166 (`opcode.py`), whose STATIC wall set is now
EMPTY. So the slice is worth **+1 stdlib file, and no more** — priced
before building, per §RANK BY `sole`, THEN PRICE THE WINNER. It is
bought anyway because that one file is the one the whole tail batch has
been walking toward, and because the construct's proof cost is ZERO (see
below): the cheapest remaining thing that moves the sweep at all.

**Scope.** `str % (tuple|namedtuple|value)` with BARE `%s`/`%r`/`%d`/`%%`
conversions over the SCALAR inventory (int/bool/str/None); CPython's
single left-to-right pass; both arity `TypeError`s and the `%d`
type `TypeError` faithful and verbatim; the format minilanguage
(flags/width/precision/mapping keys) and every other conversion
character LOUD. Recorded restriction: `%q` and a trailing `%` — which
CPython answers with `ValueError` — are refused loudly rather than
raised, because deciding them means pinning CPython's whole
valid-character set and index arithmetic. A namedtuple RHS SPREADS
(`PyTuple_Check` on the subclass, measured); treating it as one argument
would fabricate an arity error for a program CPython runs, so that arm
is required, not optional.

**Cost.** One `evalBinOp` arm + four workers; ZERO theorem arms
(`fuelMono`/`worldInv`/`clockErase` handle `binOp` generically and never
case on the operator — the `BinOp:BitAnd` precedent, §the tail construct
4); no extractor edit, no envelope re-extraction for the operator; no
mutual-block member. The ONE structural edit is a verbatim MOVE of the
scalar rendering primitives (`hexDigit`/`hex2`/`reprQuote`/`reprChar`/
`reprChars`/`reprStr`/`strOfVal`) above the operator block, because
`evalBinOp` precedes §rendering: the alternative was refusing `%r` of a
str, a boundary manufactured by file order rather than semantics.

### PRE-REGISTERED flip prediction (written before building)

**opcode.py DOES flip, outright — there is no wall behind `%`.** This is
measured, not predicted from reading: `/usr/lib64/python3.9/opcode.py`
with line 36's `%` replaced by an in-tier constant runs END TO END under
master's binary and MATCHES CPython 3.9.25, values included (a probe
inserted before the trailing `del` prints
`256 POP_TOP <op> 9 119 12 90 [100] 144 90 ('<', '<=', '==', '!=', '>',
'>=')` on both sides). The whole chain behind the wall — the guarded
`from _opcode import stack_effect` (Pass 0, except path, the §2.5
divergence that stays invisible because `__all__` is never printed),
`__all__ = [...]`, the `range(256)` comprehension, 119 `def_op`-family
calls mutating module globals through function bodies, and the trailing
`del` of the four defs — is already in tier.

Predicted numbers: stdlib sweep **7 → 8 MATCH / 159 → 158 REFUSE,
0 DIVERGE, flip set exactly {opcode}**; in-repo survey flip set among
EXISTING files EMPTY (no in-repo file walls on `%`), 97 → 99 MATCH of
121 with the two new scripts; script corpus 55 → 57 rows, 44 → 45
matched, 11 → 12 loud; diff_test 0 failed with the new str_lab/seq_lab
rows matching. Anything else — a second stdlib flip, an in-repo flip, or
opcode refusing on something other than `%` — is a finding.

### LANDED (master, 2026-08-14, the box cycle) — the semantic prediction EXACT, one arithmetic MISS

**`opcode.py` FLIPS.** `tools/leanpy /usr/lib64/python3.9/opcode.py`
exits 0 and `--compare` answers MATCH — the file the whole tail batch
(Pass 0 imports → def aliasing → `list.insert` → `del` → `%`) was
walking toward now runs end to end under the verified interpreter.

Build 3659 jobs, ZERO errors, with exactly ONE battery-caught fix, and
it was the acceptance signal itself: the build's only failure was
`Tests.lean`'s interpreter-level regression guard
`#guard isUnsupported (ev (bo (sL "%d") .mod (iL 3)))` — the line that
pinned `%` as out of tier. It now decides, so the guard records the
decided values (bare argument and the opcode 1-tuple shape) and keeps a
still-loud `%5d` row in its place. Nothing else in 3659 jobs moved:
**ZERO proof arms, as designed** — `fuelMono`/`worldInv`/`clockErase`
never case on the operator.

Verification (box, oracle CPython 3.9.25 stamped on every instrument):
extractor units 65/65; docs_check 67/67; diff_test **1213 cases, 0
failed** (1109 matched, 104 whitelisted — the 54 new rows land as
registered, the seven loud-frontier rows pinned); script_corpus
**57 scripts, 0 failed, 45 matched, 12 loud-blocked** (`fmt_script` the
opcode shape MATCH, `fmt_width_script` LOUD); in-repo survey
**121 files — MATCH=98, REFUSE=23, 0 DIVERGE**; stdlib sweep
**166 files — MATCH=8, REFUSE=158, 0 DIVERGE, flip set exactly
{opcode}** (bisect, stat, sunau, chunk, nturl2path, `__phello__.foo`,
`_sysconfigdata…`, **opcode**).

**Pre-registered vs measured.** The semantic claim held exactly:
opcode flips outright, the flip set is exactly {opcode}, the in-repo
flip set among existing files is empty, 0 DIVERGE everywhere, script
corpus 57/45/12 to the row. ONE MISS, recorded rather than quietly
corrected: the in-repo COUNT was pre-registered as 99 MATCH / 22 REFUSE
and measured 98 / 23 — an arithmetic slip in a derived number (the
deliberately-loud new script was added to the MATCH column). The claim
it was derived from — no existing in-repo file walls on `%` — is what
the measurement confirms.

**The frontier after the flip** (stdlib dynamic telemetry, first wall
per file): class-creation 106, `Import` 33, `ImportFrom` 9,
`try/except … else` 2, then singletons. Unchanged in shape from the
`del` landing — and both leaders were already PRICED and demoted
(§the import ceiling: 0 of 154 import-blocked files have a pure-Python
closure, and the class tier sits behind a module system). The cheap
single-construct tail is now spent; the next real move is a priced
tier, not another construct.

Tripwire: the two live matches ran 483 → 600 and 59 → 178 games during
the cycle with 0 forfeits, 0 illegal.

INSTRUMENT FINDING (recorded, not fixed here): an envelope's
`frontend.version` stamps the EXTRACTING interpreter, so re-extraction
on another host dirties the tree even when the AST payload is
byte-identical — three tracked envelopes currently carry a **3.14.5**
stamp from a laptop extraction, although the tier is specified against
3.9. Harmless today (the payloads agree), but it means `git status`
after a routine `script_corpus` run is not a reliable
extraction-determinism signal. The honest fix is a 3.9-family check in
the extractor; it is not this lane's scope.

## THE CLASS-CREATION WALL — CENSUSED, DESIGNED, AND PRICED AT ZERO FLIPS (2026-08-14)

Design recorded: docs/memory-model.md §the class tier. Instrument:
`harness/class_census.py`; machine-readable output
`docs/class-tier-census.json`. **Design pass only — no interpreter change
landed here.** The implementation runs on a GO from the coordinator, and
the recommendation below says what that GO is buying.

### Why this lane exists

After the `%` landing the dynamic first-wall telemetry reads
`class-creation` 106 of 166 stdlib files — the largest number on the
page, and the `%` lane's own verdict was "the cheap single-construct tail
is spent; the next move is a priced tier, not another construct." So the
class tier got priced. Per §THE SEQUENCING PRINCIPLE the pricing came
BEFORE the building, and per §RANK BY `sole` the headline number was
treated as a suspect until an instrument re-derived it.

### The instrument, and its gate

`harness/class_census.py` reads the BRICKS of the wall: per top-level
class the base form, the class-body statement kinds, the
metaclass/decorator flags; per file the minimal admissible TIER that
clears its class wall and whether clearing it would FLIP the file or
merely uncover the next wall.

Ground truth is never re-implemented: the wall predicate is the
extractor's own `creation_effects`, obtained by importing
`extractors/python/extract.py` and converting each top-level statement —
the same field `leanpy_survey.census` reads and `Json.lean`'s
`parseClassDefn` re-checks. Only the census DIMENSIONS are the tool's own
analysis, and they are cross-checked against that ground truth on every
real file.

The gate (`--controls`, run before every census, aborting on failure): 19
synthetic fixtures with hand-computed verdicts — plain methods, a literal
attribute, a computed attribute, `__slots__`, an `object` base, a
same-module base, `Exception` vs `ValueError`, two bases, a metaclass, a
class decorator, a dotted base, a `namedtuple` base, a decorated method,
control flow in the body, a nested class, a bare call — plus three real
files (`graphlib` walled with 3 classes, `opcode` and `bisect` clean).
And the cross-check itself, over the whole corpus: **unexplained demands
≠ ∅ ⟺ `creation_effects`, 0 violations over 679 top-level stdlib
classes.**

### THE FINDING THAT IS NOT A NUMBER: the third door is open

`creation_effects` closed `class C: print("x")` and `class C(base())`.
It does not close **a decorated METHOD**: both the extractor and
`classBodyStmtPure` skip a `FunctionDef` unconditionally, decorator list
and all, so a decorator with an observable effect runs under CPython and
never under the model — a wrong answer, not a refusal, in the one place
the flag exists to prevent it.

Measured: 15 creation-pure classes in 14 seed files carry a decorated
method, 2 of them (`shlex`, `sre_parse`) in files the class admission
admits today. All 15 decorate with `property`/`setter`/`classmethod`/
`staticmethod`, which have no creation-time effect — the model is LUCKY,
not sound.

**RECOMMENDED SEPARATELY AND IMMEDIATELY, tier or no tier:** count a
decorated method as a creation effect (one clause in the extractor's body
loop, one in `classBodyStmtPure`). Cost: those 2 files lose their class
admission. Flips: none — neither is a MATCH. It closes the door.

### The census (pinned 3.9 Lib; this laptop 167 seeds at 3.9.19, the box 166 at 3.9.25)

**SEEDS — the stdlib sweep.** 125 of 167 files define a top-level class;
**103 are CLASS-WALLED**; 635 top-level classes in them, **527
creation-impure (83%)**. Class-creation is the file's ONLY wall in **0**.
74 of the walled files instantiate one of their own classes at module
level; 13 never name them at all; 19 also nest a class inside a function
or class body (which `classesCreationPure` cannot see — it reads
`Module.classes`, i.e. top level only).

Base forms over the 527: no base 100, ONE base 392, two 32, three-plus 3.
The single-base breakdown is the design's whole justification —
**same-module class 285**, dotted 38, `object` 38, exception 36, imported
name 26, builtin type 20, other name 12, subscript 5, call 3, namedtuple
2. Single inheritance from a class defined in the same file is more than
half of everything.

Class-body statement kinds over the same 527 classes: `def` 403,
docstring 367, **decorated def 129**, **`__slots__` 107**, literal assign
81, name assign 62, call assign 54, display assign 35, `pass` 28,
attribute assign 17, operator assign 13, complex target 6, async def 5,
`if` 8, nested class 4, comprehension assign 3, annassign 1, `del` 1,
bare expression 1. Decorator inventory: `property` 71, `classmethod` 48,
`abstractmethod` 33, `setter` 9, `staticmethod` 8, `_tp_cache` 7,
`cached_property` 4.

**LIBRARY — the 141 pure-Python modules in the seeds' import-time
closures.** 87 class-walled, 541 top-level classes, 450 impure (83% —
the same ratio), same base ordering (same-module class 236, `object` 52,
dotted 43).

### THE LADDER, and the column that decides it

Cumulative tiers, pre-registered in the instrument before the run.
"cleared" = the file's class wall goes away; "FLIPS" = it also has no
other wall (library column discounts `import`, the wall the layer below
answers).

| step | seeds cleared | seeds FLIPS | library cleared | library FLIPS* |
| --- | --- | --- | --- | --- |
| T0 today | 0 | 0 | 0 | 0 |
| T1 body executes, no base | 3 | 0 | 2 | 1 |
| T2 + `object` base | 4 | 0 | 5 | 2 |
| T3 + same-module base | 9 | 0 | 11 | 3 |
| **T4 + builtin exception base = v0** | **24** | **0** | **16** | **3** |
| T5 + `__slots__` | 28 | 0 | 18 | 3 |
| T6 + decorated methods | 31 | 0 | 23 | 3 |
| T7 + imported/dotted base | 42 | 0 | 32 | 5 |
| T8 + builtin-type base | 47 | 0 | 38 | 5 |
| T9 + multiple inheritance | 50 | 0 | 42 | 5 |
| T10 + metaclass/decorators/dunder bindings | 78 | 0 | 65 | 8 |
| T11 + EVERYTHING | **103** | **0** | 87 | 8 |

Greedy set cover over the 103 (the honest curve, not a frequency list):
`base:exception` 6, then same-module base +5, call assign +5, name assign
+4, dotted base +6, decorated def +6, `__slots__` +7, `object` base +5,
display assign +6, builtin-type base +6 — 56 of 103 after ten features,
69 after fourteen. Same shape as every tail ranking: it COVERS, slowly,
and no single feature is worth more than 7.

**READ THE FLIPS COLUMN.** A class tier admitting every form Python has
clears all 103 class-walled seeds and flips **zero**. The six nearest
misses — `abc`, `code`, `getopt`, `io`, `py_compile`, `string`, whose
only walls are `class-creation` and `import` — are all C-REACHING, so a
Python-only module system underneath frees none of them either. The one
class-walled seed that imports nothing, `graphlib`, has four more
constructs behind its class wall (`del d[k]`, an f-string `!r`, a walrus,
a `Starred`).

**So the 106 is a cliff of ADMISSION ORDER, not of reach** —
`classesCreationPure` is `runScript`'s FIRST check, so 106 files stop
there and would stop somewhere else tomorrow. This is the import-ceiling
verdict a second time, reached by a second instrument, and it is the
third milestone `sole` has demoted.

### The v0 tier, in one paragraph

Class creation becomes an EXECUTION: the `class` statement returns to
`Module.topLevel` as a marker (the last SKIP the one pipeline left
standing), its body runs its non-`def` statements through the existing
`execStmts` in a fresh frame, and the frame's locals are merged into the
enclosing frame under `"<class>.<attr>"` — the method-flattening trick
reused, so there is no new `World` component, no new heap object kind and
no new `RVal`. Bases: single only, resolved statically at ingestion, and
only `object` / a same-module class / a builtin exception name;
everything else loud. Body: `pass`, docstring, undecorated `def`, a
plain non-dunder NAME assignment, a bare expression statement. The
exception-base row — the ladder's biggest single step, +15 seed files —
admits CREATION only and leaves the class UNINSTANTIABLE (`E("msg")`
loud: CPython's `BaseException.__init__` sets `args`, and a plain
`Obj.instance` would fabricate an object that is neither); `raise E` and
`except E` stay as loud as today, and `class N(Exception): pass` keeps
the exceptions tier's own path. Loud, each
for a stated reason: decorated methods, `__slots__`, any dunder binding,
comprehensions/lambdas/nested classes (a class body is not a closure
scope), control flow, `metaclass=`, class decorators, multiple bases,
`super()`. Lookup walks the single-inheritance chain;
`classesCreationPure` becomes `classesAdmissible` = `creationPure ∨
creationExecutable`.

### The price — and the induction question, answered at the statements

**ZERO new conjuncts in all three 18-conjunct inductions.** Verified by
reading the theorem statements, not inferred: `fuelMono` (Obs.lean, 18),
`worldInv` (11) and `clockErase` (18) quantify over the SEMANTICS mutual
block only, and Script.lean's executor is its OWN mutual block appearing
in none of them. Class-body execution lives there.

* `Stmt` gains one constructor → **17** match sites naming `Stmt.pass`
  explicitly, the proxy for a constructor-enumerating match (7
  Semantics.lean, 8 Json.lean, 2 Script.lean), most still with
  catch-alls; one-liners.
* `execStmt` REFUSES it (a class in a function body is out of tier), so
  each induction gains ONE case inside an existing conjunct —
  `Run.le_refl`, `simp at h` on `Stmt.heapFree = false`, a `clockErase`
  leaf pair. The `del` landing's pricing, one notch cheaper.
* `worldInv` is VACUOUS on the tier: `Module.heapFree` already demands
  `classes = #[]`.
* Script.lean gains one mutual member (`execScriptClass`); no
  meta-theorem quantifies over that block.
* The real proof work: `attrReadPlan`/`attrCallPlan`'s chain walk and the
  frame theorems' side conditions restated over it — small, because in
  the heapFree fragment every chain is empty.
* The NEW loudness: class attributes are `CallsIn`-visible and
  `CallsTo`-invisible (a fresh world has no namespaces), so an attribute
  miss on an instance whose class has a static attribute set must refuse
  on the value boundary rather than fabricate an `AttributeError`. The
  namedtuple boundary refusal is the precedent.

Size, by analogy to landed tiers — bigger than `del` (one constructor,
two censuses, zero conjuncts) and smaller than the exceptions tier (a new
`PyErr` constructor, two statements, a whole judgment): Ast.lean 1
constructor + 3 `ClassDefn` fields; Json.lean the biggest edit (base
resolution, chain + cycle check, `creationExecutable`,
`classBodyMethodClean`, and `parseModule` putting the marker back);
Semantics.lean one refusal arm, the chain walk in two plans, the chain
`__init__`, ~7 walker one-liners; Script.lean one mutual member and the
admission rename; Obs.lean/ClockErase.lean three one-line cases. Estimate
**700–1000 lines of Lean over five files**, ~150 of extractor, ~40
battery rows. Build-cost poles, in order: (1) the `attrCallPlan` chain
lemmas the frame theorems consume; (2) `parseModule`'s restructure, which
every ingestion census reads; (3) the 17 match sites.

### PRE-REGISTERED flip prediction (written before building)

* **stdlib sweep 8 MATCH / 158 REFUSE → 8 / 158, flip set EMPTY.** What
  moves is the wall census: `class-creation`'s first-wall count falls by
  the 24 v0 clears and rises by the 2 the third-door fix newly walls —
  **106 → 84 ± 1** — with `Import` up by 24. ANY match flip is a finding.
* **in-repo +2 MATCH**, and they are exactly the two class-walled in-repo
  files (measured: v0 clears 2 of 2, neither has another wall):
  `cls_lab.py` and `cls_effect_script.py` — the file that PINS the
  class-creation refusal. Its class-body `print` stops being refused and
  starts being REPRODUCED. That is the arc closing; the refusal pin moves
  to the new boundary. 98/23 → 100/21 among existing files.
* script corpus +6 rows (3 matched, 3 loud); diff_test 0 failed with the
  new `cls_lab` rows.
* library reach unchanged at v0 clears 16 of 87.

### RECOMMENDATION

1. **Ship the third-door fix now**, independently of any GO. It is a live
   silent-divergence hole, the fix is two clauses, and it flips nothing.
2. **The v0 tier does not pay for itself on the sweep** — zero flips, and
   that stays true at T11. If it is built, it is built for the library
   batch (87 of 141 pure-Python modules are class-walled, behind a module
   system priced at single digits) and for the LANGUAGE surface:
   inheritance is the biggest remaining hole in the class model and
   `CallsIn` over an inheriting class is a theorem shape this project
   does not have. Both are legitimate reasons; neither is a sweep number.
3. If the answer is coverage, the census says the class tier is a BATCH
   member exactly like `Starred`/`With`/`Constant:bytes` — §THE
   SEQUENCING PRINCIPLE applies, and the batch is what should be priced,
   not this tier alone.

## THE THIRD DOOR CLOSED — a decorated method is a creation effect (2026-08-14)

Scope: coordinator GO on recommendation 1 of §THE CLASS-CREATION WALL,
and on **exactly** that. The v0 class tier stays design-only pending the
batch decision; nothing here starts it.

**The hole.** `ClassDefn.creationPure` shut two doors — a class-body
statement (`class C: print("x")`) and a base expression (`class
C(base())`). A third stood open: the extractor's body loop
(`if isinstance(s, ast.FunctionDef): continue`) and ingestion's
(`if k == "FunctionDef" then pure true`) each skipped a method
UNCONDITIONALLY, decorator list and all. `@log def m(self)` CALLS `log`
at the `class` statement; the model executes no class body, so it printed
nothing where CPython prints — a WRONG ANSWER, not a refusal, through the
one door the flag exists to guard.

**The change.** Both clauses, plus the message.

* `extract.py`: a `FunctionDef` in a class body sets `creation_effects`
  when it carries decorators; every decorated `FunctionDef` also emits the
  structured flag `has_decorators` (the `has_global`/`is_generator`
  family).
* `Json.lean`: `methodCreationPure` reads that flag and `parseClassDefn`
  consults it instead of answering `pure true`. Deliberately NOT
  `args_unsupported`: it is a comma-joined MESSAGE mixing "decorators"
  with `*args`/`**kwargs`/defaults, and an unusual SIGNATURE is refused at
  CALL time while doing nothing at the `class` statement. Purity is not
  decided by matching on prose.
* `Script.lean`: the refusal now names "a decorator on the class OR on one
  of its methods", so the dynamic census can see the demand it creates.
* `FunctionDefn` is UNTOUCHED — the flag is read off the raw JSON node, so
  no positional field moves and `py_vcgen` keeps reading the body at
  field 6.

**PRE-REGISTERED prediction (written before the cycle).**

* **Zero MATCH flips anywhere.** This narrows an admission; it cannot make
  a refusing file run.
* **stdlib sweep: 8 MATCH / 158 REFUSE unchanged; −2 admitted files.**
  `shlex` and `sre_parse` move from class-admitted to class-walled (both
  refuse today on other walls, so neither is a MATCH), taking the static
  `class-creation` wall count 103 → 105 on the laptop's 167-seed 3.9.19
  set and the dynamic first-wall count **106 → 108 ± 1** on the box's 166
  at 3.9.25.
* **in-repo: no existing file changes.** Censused before building —
  0 third-door classes across `Examples/python/*/*.py`,
  `harness/scripts/*.py` and `vendor/cpython-3.9-lib-test/*.py`. The two
  new scripts take the in-repo survey 98 MATCH / 23 REFUSE → 99 / 24.
* **script corpus 57 → 59 rows, 45 → 46 matched, 12 → 13 loud.**
* **diff_test: 0 failed, unchanged** — the closed FUNCTION surface makes
  no claim about module stdout and no `Examples` envelope contains a
  decorated function (checked: 0 of the tracked envelopes carry one, so
  NOTHING is re-extracted).
* **Zero proof-layer movement**: no `Stmt`, no `RVal`, no interpreter arm
  — an ingestion-time flag only.

Anything else — a MATCH flip, a diff_test failure, an in-repo file
changing verdict — is a finding.

**Battery.** `harness/scripts/cls_deco_script.py` (expect `unsupported`),
carrying CPython's own output in its docstring: the contrast is the point,
because the pre-fix model printed a strict SUBSET of it.
`harness/scripts/cls_deco_args_script.py` (expect `match`) is the
precision pin — `*args`/`**kwargs`/defaults keep creation pure — and is
what goes red if the flag ever regresses to reading the message. Five new
extractor unit tests (undecorated pure, decorated impure, `@property`
impure, odd signatures pure, no flag on an undecorated def) and three
`Tests.lean` `#guard`s on `methodCreationPure` itself.

### LANDED (2026-08-14) — the semantic prediction EXACT, and ONE MISS recorded

Full cycle on the laptop (oracle CPython **3.9.19**, stamped by every
instrument; the box runs 3.9.25 and 166 seeds where this machine has 167,
so absolute seed counts differ by one and are not compared across hosts —
every claim below is PRE vs POST **on the same machine, same binary**).

* `lake build` **3659 jobs, EXIT=0**, first try. The three `Tests.lean`
  `#guard`s on `methodCreationPure` compile and hold (a failing `#guard`
  is a build error).
* `docs_check` 67/67. Extractor units **70/70** (five new).
* `diff_test` **1213 cases, 0 failed**, 1109 matched, 104 whitelisted —
  unchanged, as predicted: the closed FUNCTION surface makes no claim
  about module stdout.
* script corpus **59 scripts, 0 failed, 46 matched, 13 loud** — predicted
  59 / 46 / 13 to the row. `cls_deco_script` LOUD, `cls_deco_args_script`
  MATCH.
* in-repo survey **123 files, MATCH=99, REFUSE=24, 0 DIVERGE** —
  predicted 99 / 24 exactly. No EXISTING in-repo file changed verdict.
* stdlib sweep, run TWICE on this machine with only the extractor
  reverted between them: **PRE-fix MATCH=8 / REFUSE=159, POST-fix
  MATCH=8 / REFUSE=159, 0 DIVERGE both.** The flip set is EMPTY in both
  directions — the headline claim, measured rather than argued.
* the static class-admission count moved by exactly the predicted **−2**:
  `class-creation` present **103 → 105**, the two files `shlex` and
  `sre_parse`, both still REFUSE.
* the class census confirms the door: **THE THIRD DOOR 15 classes / 14
  files → 0**, creation-impure classes 527 → 542 (+15, the same 15), and
  the ground-truth cross-check is now STRONGER — it passes with 0
  violations over 679 classes *without* the decorated-method exemption it
  used to need.

**THE MISS, recorded rather than quietly corrected.** The pre-registered
DYNAMIC first-wall movement was **+2**; measured **+1** (105 → 106 on this
machine). The static movement was +2 as predicted, and the difference is a
mechanism this lane had already written down and then failed to carry into
the prediction: `sre_parse` was ALREADY refusing on class creation before
the fix, through the ingestion DEMOTION path (a recognized
`Exception`/`namedtuple` candidate that the module census demotes gets
`creationPure := false`), so it was dynamically class-walled while
statically class-pure. Only `shlex` — which refused on
`unsupported statement 'Import'` before — is new to the bucket. The
census's own RECONCILIATION line prints exactly this set and its count
dropped 7 → 6 across the fix; the prediction should have been read off it.
Restated for the box: expect its dynamic `class-creation` row to move by
**+1**, not +2, and its MATCH count not at all.

**A SECOND MISS, in the instrument rather than the semantics.** The
pre-registration said "0 envelopes re-extracted", meaning no envelope's
AST payload changes — true, and no tracked envelope gained
`has_decorators` (none contains a decorated function). But running
`script_corpus.py` REWRITES the tracked envelopes beside their sources,
and on this host that flips `frontend.version` 3.9.25 → 3.9.19 in 53
files with byte-identical payloads. That is the INSTRUMENT FINDING
recorded at the `%` landing, hitting for the second time. The churn was
reverted, not committed; the honest fix is still a 3.9-family check in the
extractor, and it is still not this lane's scope.

**Acceptance signal.** The census's own control fixture was the thing that
went red: `decorated method — THE HOLE` asserted `creation_effects=False`
and the fix made it `True`, aborting the census exactly where it should.
It is now the guard `decorated method — THE THIRD DOOR`, asserting `True`,
plus a new `undecorated method with odd signature stays pure` row beside
it, and the report line prints `(CLOSED 2026-08-14 — anything but 0 is a
REGRESSION)`.

The v0 class tier remains DESIGN-ONLY, pending the batch decision.

## The C tier: architecture DESIGNED, implementation OWNER-GATED (2026-08-15)

C as the project's THIRD modeled language — after Python and
SystemVerilog — scoped against the full C23 standard (ISO/IEC 9899:2024)
per the owner's directive, so the architecture holds as the tier
expands. The memo is
[docs/c-tier-architecture.md](c-tier-architecture.md). **Nothing is
built and no Lean exists**; the memo's job is to fix the choices that
cannot be retrofitted and leave the rest to the ladder.

**This is NOT the question the two parked C memos ask, and the memo says
so first.** `docs/c-extension-bridge-census.md` priced
C-AS-A-PYTHON-BRIDGE (model C plus CPython's C API to execute
`_struct.c`); `docs/c-intrinsics-proposal.md` priced the name-only
alternative. Both stay gated and nothing here unblocks either. This is
C-AS-A-FIRST-CLASS-LANGUAGE: its own corpus, its own oracle, its own
differential claim, answering to the standard rather than to CPython's
interior.

**The 2026-08-07 entry's precondition has been MET.** §"A C surface"
recorded *"No sunfish deliverable attached … unless a classic C sunfish
ever exists (none is planned)."* One now does: `tools/ctwin/sunfish.c`
in the sunfish-packed checkout (1310 lines, sha256 `66c569c1…`), a
node-identical TRANSCRIPTION of classic `sunfish.py` whose fidelity is a
continuously-enforced gate, not a claim. The memo argues that makes it a
semantics corpus rather than a second engine and proposes the flagship
role; **amending that scope decision is the owner's call**, stated as
open question 2. The same entry guessed the tier would be *"Clight-like:
no `setjmp`"* — the census OVERRIDES that guess (the corpus uses it) and
the memo resolves it instead of pretending otherwise.

**The census, measured** (`clang -std=c23 -D_FORTIFY_SOURCE=0 -Xclang
-ast-dump=json`, Apple clang 17.0.0, filtered to the corpus by clang's
sticky `loc.file`): 1236 non-blank lines; 54 functions with bodies (53
`static` + `main`); 50 file-scope objects; 13 structs, 7 typedefs, 3
anonymous enums; **45 distinct AST node kinds** — the whole v0
vocabulary; 2732 implicit conversions in 8 `castKind`s; 19 indirect
calls through the `movecb` callback; 7 `goto`, 3 labels, and **zero
`switch`**; 27 libc names over 124 call sites. The census is stated
under the PINNED PROFILE and the reason is itself a measurement: under
this host's DEFAULT headers the same file censuses as 48 kinds and 2764
conversions, because `_FORTIFY_SOURCE` rewrites four libc calls and
injects `__builtin_object_size`. Seven findings move the design. **NO
type punning and no unions** (the 78 explicit casts are 40 `NULL` and 38
arithmetic; the 46 implicit `BitCast`s are `void*` conversions) — so the
effective-type wall never fires on the corpus, which is exactly when it
is cheap to install right. **No `__int128`** (the accumulator is
`uint64_t`), no `_Atomic`, no `volatile`, no VLA, no `_Generic`.
**`malloc` is v0, NOT rung 2** — the directive asked the census to check
and the answer is no: all five allocation sites and all five frees are
on the search path, and `realloc` MOVES the transposition table, so the
corpus exercises provenance transfer in its hottest structure.
**`setjmp`/`longjmp` is used, and the v0 slice never takes the
transfer** (`go_depth` zeroes both caps at L894 before the `setjmp` at
L895; both `longjmp` guards are false). **The float need is exactly the
clock, and it is guarded** — the fixed-depth path evaluates ONE float
operation, `deadline != 0.0`, with no rounding anywhere. **The C twin
and the Python twin hit the same wall at the same node and the C side is
strictly easier**: `sunfish.py:322` calls `time.time()` at node 2048
(the pass-5/6 frontier), while `sunfish.c:683-685` short-circuits on
`deadline != 0.0` and never reads the clock, so Lean-C should reach
arbitrary fixed depth on an EMPTY trace where Lean-Python needs the
armed pair.

**The five architecture decisions.** (1) **Memory model**:
provenance-carrying objects — pointer = `(object, offset)` with no
integer address to lose provenance to — over byte-representable objects
with a three-way byte lattice (`conc`/`ptr`/`indet`) and per-byte
effective types; the CompCert/CH2O/Cerberus family. The v0 object-kind
set is five kinds while the TYPE already fits C23. (2) **Semantic
latitude**: UB → loud refusal, eleven classes armed at v0; unspecified →
**canonical left-to-right EXECUTION plus a commutativity CENSUS**, not
Cerberus-style exploration, because every downstream artifact
(`fuelMono`, `#py_check`, the one-line-per-job batch protocol) needs a
FUNCTION and because the census makes the canonical order EXACT rather
than lucky — measured, 64 of 828 full expressions are candidates, 32 of
them `x = f(…)` with one effect position, leaving 32 for the may-alias
check; implementation-defined → a **pinned PROFILE** versioned like the
CPython pin. (3) **Front end**: translation phases
1-6 outside Lean via `clang -Xclang -ast-dump=json` (the house
third-party-frontend rule, plus: using the oracle's own parser makes
front-end agreement structural, and clang MATERIALIZES all 2732 implicit
conversions so the ingester never re-derives one); Lean owns phase 7.
(4) **Oracle + harness**: pinned clang at `-O0` with
`-fsanitize=undefined,address -fno-sanitize-recover=all` as the raise
channel, the `jobs.jsonl` batch protocol in two dialects, and **THE
SQUARE** — Lean-C ≡ compiled-C ≡ CPython ≡ Lean-Python on node identity.
(5) **Effect walls**: `setjmp` admitted in its four legal syntactic
contexts returning 0 with `longjmp` LOUD (sound because the transfer can
never be taken, so the 0 return is never wrong — the poisoned-binding
shape); stdout modeled as world data; stdin/`getenv`/clock as INPUT
TRACES (the trace-clock precedent); floats an **EXACT-ONLY tier** in v0
with IEC 60559 as a named rung; threads/`volatile`/signals/VLA out by
kind.

**Two measurements that the design turns on, both recorded because they
are counter-intuitive.** First, **`-fno-sanitize-recover=all` is
REQUIRED**: by default UBSan prints its diagnostic and CONTINUES with
the wrapped value (measured — the `INT_MAX + 1` probe printed
`-2147483648` after its diagnostic), so an oracle that runs past UB
produces a value the model refuses and the row reads as a DIVERGENCE
when it should read as a REFUSE. Second, **no sanitizer detects strict
aliasing or uninitialized reads on this host** — measured across
`-fsanitize=undefined`, `-fsanitize=address`, and both — which is
exactly why effective types and the `indet` byte have to live in the
MODEL rather than in the raise channel. Honest environment note: **ASan
binaries do not run in this sandbox** (a trivial `main` built with
`-fsanitize=address` times out), so that channel is DESIGNED and must be
verified on the build box, not assumed.

**The `frontend.version` lesson applied, and the C case is worse.**
Recorded twice in this file already (3.9.25 ↔ 3.9.19 churn, byte-identical
payloads, 53 files the second time). Correction one: stamp the compiler
FAMILY, never the point release. Correction two, C-specific: **the system
headers change the PAYLOAD.** Measured — with Apple's default headers,
`_FORTIFY_SOURCE` rewrites `memcpy`/`strcpy`/`sprintf`/`snprintf` into
`__builtin___*_chk` and injects **10 `__builtin_object_size` nodes that
are in nobody's source**; with `-D_FORTIFY_SOURCE=0`, zero of each. So
the profile is an INPUT to the AST, `profile_id` is a first-class
envelope field, the ingester refuses a profile mismatch loudly, and the
cache key gains the profile alongside the existing `extractor_digest()`.

**v0 price, by analogy to the measured lanes** (Python 23,306 Lean lines
— 10,554 interpreter core, 11,550 proof layer; SV 8,166; extractors 1512
and 2495): **~7,000-11,000 Lean + ~2,000-3,000 Python**, bracketing
between the two lanes — correct, because C's semantics is larger than SV
M0's and **v0 builds NO proof layer at all** (no VC walker, no tactics,
no theorem surface; that is 11,550 of the Python lane's lines v0 does
not write). Five build poles: extractor+schema+profile (no Lean) → Ast
and ingester (no semantics) → memory model and WF (no interpreter) →
interpreter and batch arms → the battery.

**The three first battery milestones. M0 costs zero Lean**: `difftest.py`
currently drives `sunfish.py` under **pypy3** via `pyref.py`, not the
pinned CPython 3.9.19, so the square's existing edge is
A ≡ pypy3(sunfish.py) and not A ≡ C — re-run it under the pinned oracle
and the square either closes or finds something today. **M1**: the ten
scalar leaves under `--c-batch` with the raise channel armed, which is
also the square's first cross-language datum, because `pyfloordiv`/`pymod`
are the exact site the ctwin README names as the #1 silent-divergence
class. **M2**: `gen_moves` order — one call exercising the callback, the
struct, the board, the macros, the static tables and the `indet` rule,
with the comparison format already defined by `difftest.py`.

**Ladder**: v0 (the fixed-depth corpus) → R1 statement completion
(`switch`) → R2 layout (unions, punning, bit-fields) → R3 nonlocal
transfer (`longjmp`) → R4 floats (gated on a toolchain that DEFINES
`__STDC_IEC_60559_BFP__`; the candidate oracle does NOT) → R5
variably-modified types → R6 concurrency, deliberately LAST because it
is the one rung that replaces the state function with a memory-order
relation → R7 the rest of C23.

**GATED: nothing in the memo may be built until the owner answers its
three open questions** — whether the lane gets `LeanModels/C/` and a
`leanmodels-c-run` exe (touching the two files AGENTS.md fences off),
whether the 2026-08-07 "no sunfish deliverable" scope decision is
amended, and which host is the pinned oracle (the profile must be pinned
BEFORE the extractor is written, since it is an input to the AST).

## The square's FRONTEND edge — measured, and it was the unpinned one (2026-08-15)

Opened as this repo's half of the C-tier memo's **M0** (§The C tier,
"M0 costs zero Lean"). The memo's M0 names `tools/ctwin/difftest.py`,
which lives in the SUNFISH repo and drives `sunfish.py` under pypy3 via
`pyref.py`; **that re-run is still owed and is not what this entry
records** (see the last paragraph). What this entry records is the same
question asked of THIS repo's own instruments — and the answer is not the
one the memo's phrasing predicts.

**The premise, corrected first.** lean-surfaces' Python harness does not
drive pypy3, and did not when the recorded sweeps were taken.
`harness/diff_test.py` re-execs into the pin (`_reexec_under_pinned_cpython`,
`want = "python3.9"`, landed 2026-08-13) and `harness/leanpy_survey.py`'s
`default_oracle()` returns `python3.9` whenever it is installed. Both
instruments stamp the oracle they used and every recorded run stamps
3.9.19. **The ORACLE edge was already honest.**

**The oracle edge, measured anyway** (this laptop, `leanmodels-run` at
b525023, corpus held FIXED and only the oracle binary varied — CPython
3.9.19 vs PyPy 7.3.23 / 3.11.15):

* in-repo survey, 123 files: MATCH=99, REFUSE=24, 0 DIVERGE under BOTH.
* stdlib sweep, the 167 pinned 3.9 seeds passed as explicit paths so the
  corpus could not move: MATCH=8, REFUSE=159, 0 DIVERGE under BOTH.
* Diffed file by file on seven axes (verdict, status, exit, msg, detail,
  live, nodes): **0 differences over all 290 files.** The difftest
  interpreter is VERDICT-INVARIANT across pypy3 and the pinned CPython on
  the current corpora.

**What that claim does NOT cover, stated because the harness makes it
easy to overstate.** REFUSE is decided *before* the oracle runs — in
`leanpy_survey.py` a `status == "unsupported"` row takes its verdict and
`continue`s above the `run_cpython` call. So of the 290 files only **107**
(99 + 8) ever invoke an oracle binary; the interpreter choice can move the
MATCH/DIVERGE partition and nothing else. The invariance measured is
exactly: on the 107 files that reach an oracle, the two interpreters
produce the same stdout and the same exit code.

**`--stdlib --cpython pypy3` is a DIFFERENT EXPERIMENT, not the same one.**
`stdlib_seeds` derives from `ModuleTable.of(opts.cpython)`, so the sweep's
CORPUS is a function of the interpreter: under pypy3 it becomes PyPy's own
`lib-pypy3.11` — 228 files, 5 MATCH / 9 DIVERGE / 210 REFUSE / 4 EXTRACT.
The 9 DIVERGE are all PyPy's private cffi build scripts (`_curses_build`,
`_lzma_build`, `_syslog_build`, `marshal`, …) where the model raises
`ModuleNotFoundError` and the oracle raises a cffi build error. They are an
artifact of a corpus nobody pinned, not a model bug — recorded here so the
number is not mistaken for one later. It also exposed a **side-effect class
`import_closure.SAFETY` does not cover**: those same `_*_build.py` scripts
invoke the C compiler, so the run left 19 `_*_cffi.{c,o,so}` files in the
repo root (removed by hand). SAFETY is a list of modules that open a
browser, a window, or the network; nothing there anticipates a top level
that writes build products into the cwd. Harmless on the pinned 3.9 path,
which contains no such module — but the safety list is a denylist of names,
not a sandbox, and that is worth knowing before anyone points `--stdlib` at
a third interpreter.

**THE FINDING: the FRONTEND was never pinned, and no cache key named it.**
An envelope is a function of (source, extractor, **the CPython whose `ast`
module parsed the source**) — `envelope_for` in `tools/leanpy` runs
`extract.py` under `sys.executable` — but the cache key was
`sha256(source) + extractor_digest()`, naming only the first two. And
`tools/ci.sh` runs the survey as `python3 harness/leanpy_survey.py`, where
`python3` on this laptop is 3.14.5 while the oracle is 3.9.19. Measured
over the 123-file in-repo corpus, extracting every file under both:

* **123/123 envelopes differ.** `frontend.version` is
  `platform.python_version()` — the POINT release, the exact anti-pattern
  the C-tier memo says was learned twice.
* **5/123 payloads still differ with that stamp excluded.** Three are
  span-only, from PEP 701: 3.12+ gives each f-string part its own
  sub-span where 3.9 gives every part the whole `JoinedStr` span
  (`fstring_script.py`, `fstring_lab.py`, `test_builtin.py`). Two are
  STRUCTURAL — `test_compare.py` and `test_grammar.py` — where
  `ast.unparse` reformats the `Unsupported.text` of an already-refused
  node (`lambda : True` → `lambda: True`, `for (other, _) in ops` →
  `for other, _ in ops`).
* **VERDICTS DO NOT MOVE.** The whole survey re-run under a 3.14 driver
  with a private cache is identical to the 3.9 run on all seven axes
  across all 123 files.

So it is benign today, and it was benign by luck rather than by
construction. `LeanModels/Python/Json.lean` accepts `frontend` and does
not retain it, so nothing downstream could ever have refused a
wrong-frontend envelope; the cache key was the only possible defence and
it did not mention the frontend. Two drivers sharing
`$TMPDIR/leanpy-cache` served each other's envelopes.

**LANDED (master, 2026-08-15) — code and record together.**

* `tools/leanpy`: `frontend_family()` joins `extractor_digest()`, whose
  value now ends `-py3.9`. The FAMILY and not the point release —
  re-keying every envelope for a byte-identical payload is precisely the
  3.9.19 ↔ 3.9.25 churn this file already records twice.
* `harness/leanpy_survey.py`: `_reexec_under_pinned_frontend()`, a
  deliberate mirror of `diff_test.py`'s oracle re-exec — pin `python3.9`,
  `LEANPY_FRONTEND` overrides, `LEANPY_NO_REEXEC=1` disables, and a
  missing pin WARNS LOUDLY and keeps going (CI has no 3.9). The two knobs
  stay separate on purpose: `--cpython` / `LEANPY_CPYTHON` still selects
  the ORACLE, which is how pypy3 was surveyed above.

Triad after: `lake build` **3659 jobs EXIT=0**, `docs_check` **67/67**,
`diff_test` **1213 cases, 0 failed** (1109 matched, 104 whitelisted).
Both sweeps re-run through the new key: 123 / 99 / 24 / 0 and
167 / 8 / 159 / 0 — unchanged, as the driver comparison predicted.

**STILL OWED, and not done here.** The memo's M0 proper — running
`tools/ctwin/difftest.py` under CPython 3.9.19 instead of pypy3 — is in
the SUNFISH repo (`tools/ctwin/` is not on sunfish master; it is carried
on the sunfish-packed / -eval / -tm / -eventual-trichotomy checkouts), a
cross-repo job this lane had no write scope for. Nothing above substitutes
for it: over there the edge is still A ≡ pypy3(sunfish.py).

## A silent wrong answer, closed — plus two instrument repairs (2026-08-15)

Three items off the free-standing list, smallest honest versions. The
first is the only one that was a CORRECTNESS bug, and it had been sitting
in the open as a design note rather than a defect.

### The starred assignment target answered instead of refusing

`x, *y = [1, 2, 3]` — CPython 3.9.19 binds `x = 1`, `y = [2, 3]` and
exits 0. leanpy answered **`ValueError: too many values to unpack
(expected 2)`, exit 1.** Not a refusal (exit 3): an ANSWER, and a wrong
one, in the tool whose contract is "answers loudly or not at all".

**Why it escaped.** The element check was already there and already
correct — `unpackSeq` refuses a target element that is not a plain name —
but it runs AFTER the arity check. So the refusal fired only when the
arity happened to coincide, which is exactly the case where nothing was
at stake. Measured across the shapes, before the fix:

| source | CPython 3.9.19 | model, before |
| --- | --- | --- |
| `x, *y = [1,2]` | `1` / `[2]` | REFUSE (exit 3) — correct |
| `x, *y = [1,2,3]` | `1` / `[2,3]` | **`ValueError: too many values to unpack (expected 2)`** |
| `*x, y = [1,2,3]` | `[1,2]` / `3` | **`ValueError: too many values to unpack (expected 2)`** |
| `x, *y = [1]` | `1` / `[]` | **`ValueError: not enough values to unpack (expected 2, got 1)`** |

The other three binding sites were already loud and are unchanged:
`for a, *b in …` refuses ("unpacking targets other than plain names"),
and the comprehension form refuses at lowering. **`Assign` was the only
site**, which is what keeps the fix one clause.

**The fix is the DOCTRINE, not the feature.** `extract.py` refuses the
whole statement — `_target_has_starred` over the target tree (nested
`a, (b, *c)` included) → `unsupported(node, "Starred:target")` — because
refusing the inner element alone cannot work: the model reaches the
arity check first. It costs ZERO coverage, since every starred target
already ended in a refusal or a wrong answer and never in agreement.
Real support stays a listed backlog item: designed at §Position 2 (a
`Stmt.unpackAssign` constructor carrying names) and built on the
`starred-displays` branch (eb6a882), which this deliberately does NOT
merge.

Guard: `harness/scripts/star_target_script.py`, registered
`expect: unsupported`, carrying the wrong-answer shape itself.

**Sweep delta, stated in full — the guard and nothing else moved.**

* in-repo survey 123 → **124 files**, MATCH 99 → **99**, REFUSE 24 →
  **25**. The one new row is the guard; **0 existing files changed
  verdict, on any of the seven axes.**
* stdlib sweep **167 / 8 MATCH / 159 REFUSE / 0 DIVERGE — byte-identical
  to the pre-fix run**, 0 differences.
* script corpus 59 → **60 scripts, 0 failed, 46 matched** (unchanged),
  13 → **14 loud-blocked**.
* No tracked envelope is affected: an AST scan of every tracked `.py`
  finds **zero** starred assignment targets, so the new clause cannot
  fire on anything with a committed envelope.

Triad: `lake build` 3659 jobs EXIT=0, `docs_check` 67/67, extractor units
70/70, `diff_test` 1213 cases 0 failed.

### The staleness warning cried wolf, and now reads content

`runner_command` warned whenever a Lean source's MTIME beat the binary's.
Any `git checkout` that rewrites a file to the bytes it already had trips
that, so the warning fired on every single run of a perfectly current
binary — and a warning that is usually wrong is not read, which is the
failure it exists to prevent, inverted.

Staleness is a CONTENT question. `lean_source_digest()` (sha256 over all
108 Lean sources, measured **3.8 ms**) is compared against a stamp beside
the binary. The stamp is written on either of the two SOUND observations
that the binary carries those sources: `lake build` just succeeded, or
nothing is newer than the binary by mtime. (Lake does not touch its own
`.trace`/`.hash` on a no-op verify — measured — so there is no cheaper
signal to read.) Every uncertain case still WARNS, and the message now
distinguishes them: "the Lean sources have CHANGED since it was built"
vs "no build stamp exists to say whether the content changed".

Verified in all three directions: `touch` on a source → silent; a real
one-line edit → warns; reverting that edit → silent again.

### Four stale status lines corrected

Each struck in place with where it was actually decided, because a
backlog that advertises dead gates is worse than one that is merely
incomplete. `§Pass 5`'s "standing OWNER-GATED abstraction decision" —
decided in `§Pass 6`, the very next section, and built the same day.
`§Pass 5`'s "`input` is still absent from `isBuiltinName`" — it is at
`Ast.lean:517`. `§Pass 7`'s "OPEN: a kernel-affordable concrete-run
route" — closed DEFINITIVELY by `§Pass 8` milestone 1. `§Pass 8`'s
"leanpy script-mode trace flag (pass-6 deferral)" — shipped as
`tools/leanpy --clock`, recorded at the top of this file.

### Recorded, NOT fixed: `script_corpus.py` dirties the tree

Found while validating the guard above. `harness/script_corpus.py`
extracts with `sys.executable` and **without `--out`**, so it rewrites the
tracked `harness/scripts/*.json` envelopes in place, under whatever
`python3` is on the box: one run left 44 tracked envelopes modified with
nothing changed but `"version": "3.9.25"` → `"3.14.5"`, plus 8 untracked
new ones. Reverted by hand. It is not in `tools/ci.sh`, so CI never sees
it. The fix is the one already applied to the survey — pin the frontend,
and extract to the cache rather than beside the source — but it is a
fourth item and is left open here rather than smuggled in.

## The `<<` budget, and the frontend residue closes (2026-08-15)

### `<<` had no bound — and the recorded prediction was wrong about how it failed

`evalBinOp`'s `.lshift` arm computed `x * 2^y` with nothing bounding `y`.
§`^` rides free recorded this as a live defect and predicted the model
"would sit down and try to build the number — a hang". **Measured first,
and it is not a hang.** On this toolchain `1 << (10^30)` dies
`INTERNAL PANIC: Nat.pow exponent is too big` — Lean's own `Nat.pow`
guard fires, and the runner ABORTS. So the defect is real but its shape
is a runner abort, not unbounded silence; recorded that way rather than
repeating the prediction.

What is genuinely surprising, and why the bound had to be DECLARED rather
than fitted: everything below that panics nothing and is exactly right.
Measured, model vs CPython 3.9.19, `print((1 << n) % 1000)`:

| `n` | CPython | model, before |
| --- | --- | --- |
| `10`, `1000`, `100000` | agree | agree |
| `10^7`, `10^8` | agree, ~40-60 ms | agree, ~150-180 ms |
| `10^9` | 251 ms (a real 125 MB integer) | 407 ms, correct |
| `10^30` | `OverflowError` | **`INTERNAL PANIC`** |

**The fix is the pattern that already exists.** `seqBudget = 1048576`
guards `rangeVals`/`tupleRepeat` with a fixed, therefore fuel-INDEPENDENT
`unsupported`. `shiftBudget = 1048576` is its sibling — its own constant,
as this file recorded it should be ("its own budget decision alongside
`seqBudget`"), bounding the shift COUNT so the widest result is about a
million bits. Below it nothing changes; above it the arm refuses loudly.
It joins `py_simp`'s unfold set beside `seqBudget`.

**Stated plainly: this refuses shifts CPython performs.** `1 << (10^9)`
is a real integer in CPython and is now `unsupported` here — a declared
tier gap, never a claim that CPython raises. That is the same trade
`seqBudget` already makes, and everything the corpus actually shifts
(`1 << 63`) is five orders of magnitude inside the bound.

`>>` needs nothing: `RShift` is in neither `ALLOWED_BINOPS` nor the
`BinOp` inductive, so it refuses at extraction and would inherit the
budget free if ever admitted.

**Pinned on both sides of the edge** (`Examples/python/seq_lab/spec.lean`,
checks-only so no theorem depends on the arm): `shl(1, 4096) = 2^4096`
exactly; `.ok` at exactly `1048576`; `.unsupported` at `1048577`;
`.unsupported` at `10^30`. Differentially (`harness/cases.json`):
`[1, 4096]` joins the `expect: match` group, and `[1, 10^30]` is a new
`expect: unsupported` row whose note records that CPython raises
`OverflowError` there — a documented tier gap, which is the only thing a
whitelist row may ever be.

**Gates.** The previously-panicking shape now exits **3** (LOUD REFUSAL)
in **293 ms** warm. `diff_test` **1215 cases, 0 failed** (was 1213: +1
matched, +1 whitelisted — exactly the two new rows). Script corpus
**60 / 0 failed / 46 matched / 14 loud**, unchanged. **Both sweeps moved
ZERO files**: in-repo 124 files 99 MATCH / 25 REFUSE / 0 DIVERGE and
stdlib 167 files 8 / 159 / 0, with 0 differences on all seven axes.
`lake build` 3659 jobs EXIT=0 (a full proof-layer rebuild — `evalBinOp`
is below everything), `docs_check` 67/67, extractor units 70/70.

### `script_corpus.py` pinned — and the 3.14.5 stamp residue is GONE

The item recorded above as "found, not fixed" is fixed. Two changes, the
same two the survey took: `_reexec_under_pinned_frontend()` (`LEANPY_FRONTEND`
overrides, `LEANPY_NO_REEXEC=1` disables, missing pin warns LOUDLY), and
extraction routed through `tools/leanpy`'s cache-keyed `envelope_for`
instead of a bare `extract.py` call with no `--out`.

**Both halves gated independently, because they fix different things:**

* driver `python3` (3.14.5) → re-execs to the pin → `git status` shows
  only the intended edits, **zero envelope churn**.
* `LEANPY_NO_REEXEC=1 python3 …`, frontend genuinely 3.14.5 → the tree is
  **still clean**, which is the `--out` half doing its job independently
  of the pin.
* Both report the identical `60 / 0 / 46 / 14`, one more datum for
  frontend verdict-invariance.

**The 13 tracked envelopes stamped `3.14.5` were re-extracted under the
pin, after verifying every one.** Each was classified before touching it;
all 13 came back STAMP-ONLY (payload byte-identical, no span change, no
structural change), and the resulting diff is exactly 13 lines of
`"version": "3.14.5"` → `"3.9.19"` and nothing else. Tracked
`cpython-ast` stamps are now **92 at 3.9.25 + 15 at 3.9.19, zero 3.14.5**
— the WRONG-FAMILY residue is closed. The remaining 3.9.19/3.9.25 split
is the known cosmetic point-release churn between this laptop and the
box, the same family, and this file has twice said not to chase it.
`lake build` green after the re-extraction and both sweeps unmoved.

Noted while there, not acted on: those `harness/scripts/*.json` envelopes
are referenced by **no code in the repo** — `script_corpus.py` was their
only writer and nothing ever read them. They are tracked build artifacts,
and now that extraction goes to the cache nothing writes them either.
Deleting them is a separate call.

## The payload-free `PyErr` constructors — CENSUSED, and the fix SPLITS in two (2026-08-15)

§`leanpy` v1 recorded five constructors whose CPython text the class does
not determine, as "open, the next step". Measured before touching
anything, and the census changes the shape of the work: **the five are
not one problem.** Two of them carry no runtime data at all — their text
is chosen by WHICH raise condition fired — and those are fixable at zero
cost to the spec surface. Two carry runtime data and need real payloads.
One can never be answered and should stop being counted as debt.

### The census (CPython 3.9.19, all 1215 `harness/cases.json` cases)

Raising cases by class, with the distinct texts the oracle produced:

| class | cases | distinct texts | text determined by |
| --- | --- | --- | --- |
| TypeError | 65 | 51 | already carried (`msg`) |
| ValueError | 16 | 13 | already carried |
| **ZeroDivisionError** | **14** | **2** | **the raise CONDITION** |
| AssertionError | 12 | 8 | already carried |
| **IndexError** | **11** | **4** | **the raise CONDITION** |
| NameError | 10 | 8 | already carried (the name) |
| **AttributeError** | **9** | **8** | **RUNTIME DATA** (type + attr) |
| user (`Stop`) | 4 | 2 | class alone, exact |
| **RecursionError** | **2** | **1** | **CPython's C SITE** |
| **KeyError** | **2** | **2** | **RUNTIME DATA** (key `repr`) |
| StopIteration | 2 | 1 | bare, exact |

And on the script corpus, where the survey already reports message
telemetry: **7 SAME, 0 DRIFT, 2 ABSENT** — and both ABSENT rows
(`raiser.py`, `init_raise_script.py`) are the SAME missing text,
`ZeroDivisionError: integer division or modulo by zero`.

### The finding: two of the five need no payload at all

`ZeroDivisionError`'s two texts are `integer division or modulo by zero`
(13 of 14 cases, from `//` and `%`) and
`0.0 cannot be raised to a negative power` (1 case, from `0 ** -1`).
That is not runtime data — it is a two-way static split inside
`evalBinOp`. So the fix is a sibling NULLARY constructor, not a `String`
payload, and the difference is the entire cost of the item:

| approach | sites touched | PUBLIC theorem statements changed |
| --- | --- | --- |
| `String` payload on `zeroDivisionError` | 40 | **4** (`arith`'s `floordiv_zero`/`mod_zero` + their `#py_check`s) |
| sibling `zeroDivisionPow` | **4** | **0** |

`except ZeroDivisionError:` cannot tell them apart, because builtin
exception names are not matchable in the tier at all — only admitted user
classes and the pinned import-error names — so the split is
unobservable to any program the model runs.

**LANDED (2026-08-15):** `Ast.lean` gains `zeroDivisionPow`, `errName`
maps both to `ZeroDivisionError`, `errMessage` answers both with their
measured text, `evalBinOp`'s `.pow` arm raises the new one, and exactly
ONE existing row moved (`Tests.lean:146`). No spec, no proof, no
delaborator, no handler table.

### What is left, priced

* **`IndexError` — the same trick, not yet taken.** Four texts
  (`list index out of range` ×8, `tuple index out of range`,
  `list assignment index out of range`, `pop from empty list`), all
  condition-determined. Three sibling constructors; 7 `Semantics.lean`
  raise sites to triage; keeping `.indexError` as the dominant
  list-index case leaves most of its 5 public statements untouched.
  **~1-2 hours**, and it is the next one to take.
* **`KeyError` and `AttributeError` — genuinely structural.** The texts
  interpolate runtime values (the missing key's `repr`; the type name
  AND the attribute), so no split can supply them and the constructors
  must take payloads. `reprVal` and `typeName` already exist, so the
  data is in hand at every raise site — the cost is not the semantics,
  it is the **4 and 8 public theorem statements** that would change
  shape, plus 1 and 27 `Semantics.lean` sites. **~half a day each, and
  it changes the documented spec surface, so it wants the owner's eye.**
* **`RecursionError` — retire it as debt.** CPython's text names the C
  site it hit (`maximum recursion depth exceeded in comparison`), which
  no model state determines and no payload can honestly supply. It
  should stay ABSENT permanently and be recorded as such rather than
  carried as an open gap.

### The enforcement question, answered — and NOT flipped

The tier the harness enforces is **the full `Class: message` line, exact,
and only where the model carries a message.** That is already
`script_corpus.py`'s rule and it is the right one; prefix or family
matching would hide precisely the drift the step exists to catch. So
`ZeroDivisionError` graduates to enforced TODAY, automatically, by
starting to carry a message.

**`diff_test.py` is NOT graduated, and that is a measurement, not
caution.** It compares the exception CLASS only. Tightening it to compare
messages right now would flip **24 of its 1215 cases** to failures —
every case whose class is one of the four still-payload-free ones
(IndexError 11, AttributeError 9, KeyError 2, RecursionError 2), because
the model renders the bare class where CPython renders `Class: text`.
That flip is the CONSEQUENCE of the remaining work, not a decision to be
taken ahead of it: `diff_test` should graduate when `IndexError`,
`KeyError` and `AttributeError` land, with `RecursionError` whitelisted
as permanently absent. Stated here so nobody tightens it early and reads
24 red rows as a regression.

One honest limit on this census: the classes that DO carry messages are
designed to be verbatim (`BinOp.symbol` exists so every `TypeError` comes
out exactly), and the script corpus is 7/7 SAME with 0 DRIFT — but the
typed-call layer has never had its messages compared at all. Measuring
those 100-odd carried texts against the oracle is part of graduating
`diff_test`, and this entry does not claim it has been done.

### Measured after the split

Message telemetry over the in-repo corpus, **7 SAME / 0 DRIFT / 2 ABSENT
→ 10 SAME / 0 DRIFT / 1 ABSENT**. Both former ABSENT rows (`raiser.py`,
`init_raise_script.py`) now read
`ZeroDivisionError: integer division or modulo by zero` exactly, and the
new `zerodiv_pow_script.py` reads
`ZeroDivisionError: 0.0 cannot be raised to a negative power` exactly —
so BOTH texts are pinned end to end and the split is confirmed at the
boundary, not just in the constructor. **The one remaining ABSENT row in
the whole corpus is `index_message_gap_script.py`, which exists to be
that gap.** `script_corpus.py` now ENFORCES all three lines (it compares
the whole line whenever the model carries a message): 0 failed.

Sweep delta: in-repo 124 → **126 files** (the two new pins), MATCH 99 →
**101**, REFUSE **25** unchanged, 0 DIVERGE; stdlib **167 / 8 / 159 / 0
byte-identical**. **Zero existing files changed verdict on any of the
seven axes.** `diff_test` **1215 cases, 0 failed** — unchanged, exactly
as predicted, because it still compares the CLASS only. Triad: `lake
build` 3659 jobs EXIT=0, `docs_check` 67/67, extractor units 70/70.

## `IndexError` — STOPPED at the census (2026-08-15)

A stop, taken in the order the standard requires: census first, then look
at what it costs, then decide. **Nothing was implemented and no code
changed** — this entry is the durable record of a priced, ready, and
deliberately unstarted piece of work. (`RecursionError`'s retirement is
its own entry, because it carries a `harness/cases.json` change and lands
with it.)

### `IndexError`: the earlier count of FOUR texts was WRONG. There are SIX

§the payload-free constructors priced `IndexError` at "four texts, three
sibling constructors, ~1-2 hours" from the `harness/cases.json` census.
Re-measured against CPython 3.9.19 at each of the model's SEVEN raise
sites — rather than at the cases that happen to exist — and the earlier
number was an artifact of the corpus, not a fact about `IndexError`.
**Two texts were invisible because no case exercised them**: no case
indexes a string out of range, and no case pops a non-empty list out of
range.

| model raise site | condition | CPython 3.9.19 text |
| --- | --- | --- |
| `indexVal` `.listV` (1298), `heapIndex` `.list` (1754) | list read | `list index out of range` |
| `indexVal` `.tuple` (1306), `.ntuple` (1316) | tuple read | `tuple index out of range` |
| `indexVal` `.str` (1324) | string read | **`string index out of range`** |
| `heapStore` `.list` (1788) | list ASSIGN | `list assignment index out of range` |
| `heapPop` (1861), list EMPTY | pop | `pop from empty list` |
| `heapPop` (1861), list non-empty | pop | **`pop index out of range`** |

All six are still CONDITION-determined — no runtime data — so the
nullary-sibling trick still applies and no payload is needed. But it is
**five siblings, not three**, and site 1861 needs an internal split on
`xs.isEmpty` because one raise site carries two texts.

**STOPPED, per the standing instruction, because public theorem
statements move.** Of the five public statements mentioning
`.indexError`, three are list reads and survive untouched — but **two do
not**:

* `Examples/python/list_lab/spec.lean:49` —
  `#py_check list_lab.store_error() raises .indexError`. `store_error`
  is `xs[3] = 0`, the ASSIGNMENT site, so it must become
  `.indexErrorAssign`.
* `Examples/python/list_lab/spec.lean:55` —
  `#py_check list_lab.pop_empty() raises .indexError`. `pop_empty` is
  `[].pop()`, so it must become `.indexErrorPopEmpty`.

Unchanged for the record: `arith/spec.lean:39` (`[10,20,30][i]`),
`list_lab/spec.lean:47-48` (`xs=[1,2]; xs[i]`), and both `Tests.lean`
rows — all list reads.

So `IndexError` is NOT free of spec-surface churn the way
`ZeroDivisionError` was, and that is the whole reason `ZeroDivisionError`
was taken alone. **Nothing was implemented.** The work is otherwise ready:
six texts measured, seven sites mapped, five siblings named, two
statements identified by line. It needs a decision about changing two
public statements, and that decision is not this lane's.

### THE OWNER'S FORK, stated crisply

Three things now gate the message step, and they are separate decisions:

1. **`IndexError`** — no payload, five sibling constructors, six measured
   texts, ~1-2 hours of mechanical work. Cost: **2 public theorem
   statements change shape** (`list_lab` `store_error`, `pop_empty`).
   This is the cheap one and it is blocked only on accepting that churn.
2. **`KeyError`** — needs a real `String` payload (the key's `repr`;
   `reprVal` exists). Cost: **4 public theorem statements**, 1
   `Semantics.lean` site.
3. **`AttributeError`** — needs a real payload (type name + attribute;
   `typeName` exists). Cost: **8 public theorem statements**, 27
   `Semantics.lean` sites.

2 and 3 change the documented spec surface (docs/spec-surface.md is
normative for statement shapes), which is why they are owner-gated rather
than merely large. All three are independent: taking 1 does not commit to
2 or 3, and 2 and 3 are the same kind of change at different scale.

## LIBRARY MODE — the metric, the harness, the corpus (L1, 2026-08-15)

The owner changed the completeness metric today, verbatim: library mode is
**"import this module, then verify its public functions behave identically
to CPython's"** — **"We should be able to verify modules that we just
import, but don't have a way to run."**

Program mode answers a different question. `harness/leanpy_survey.py` runs
a FILE and compares stdout and exit code, so a library — which prints
nothing — scores a MATCH for empty stdout against empty stdout. That is a
verdict about nothing, and the corpus that matters is mostly libraries:
the import-ceiling census's own denominator is 141 pure-Python modules
that exist to be imported. Library mode is the instrument for them.

### What landed (L1 — instrument only, no model change)

* `harness/library_survey.py` — the driver. TWO PHASES. **BODY**: the
  module's top level under CPython as an IMPORT (a fresh module object
  whose `__name__` is the module name) against the model
  (`--script-batch`), comparing stdout, the exception CLASS, and — where
  the model carries one — the exception MESSAGE (the message tier of the
  program-mode survey: SAME/DRIFT/ABSENT). **CALLS**: for a module whose
  body agreed, every public function THE FILE DEFINES is driven on a
  deterministic battery through `--batch` and each return value or
  exception is compared. Verdicts: VERIFIED (body + all calls, with the
  call count), BODY-ONLY (body agreed, battery empty — reported apart from
  VERIFIED, never folded into it), PARTIAL (N of M), REFUSED (the named
  construct), DIVERGED (the headline; any row fails the run).
* `harness/library_oracle.py` — the CPython half, one subprocess per
  module: import, enumerate, build the battery, run it. A subprocess and
  not an in-process import because this corpus is the real stdlib — one
  module that hangs costs one row, not the survey.
* `harness/library_corpus.json` — the manifest (below).

### Five decisions the design turns on

1. **THE IMPORT-SEMANTICS GATE.** The model has no import machinery:
   `Script.lean`'s `scriptNameBinding` binds `__name__ = "__main__"`,
   which is PROGRAM semantics. A module that never reads `__name__` at
   import time cannot tell the two apart, and only for those is a
   program-mode body run also a library-mode answer. For the rest the
   survey REFUSES with the named construct `import-semantics:__name__`
   rather than compare a program-mode run against an import-mode oracle
   and call the difference a divergence. The gate fires ONLY where the
   model would otherwise have claimed a body match, so it can never hide a
   refusal the model itself produced. This is the open import-semantics
   decision (§the module-init mutation gap, item 1) showing up as a
   measured refusal class instead of a footnote.
2. **The public surface is read from the FILE's AST, driven through the
   RUNTIME object.** `bisect.py` is the case that decides it: its guarded
   `from _bisect import *` REBINDS all four pure functions to C ones, so a
   runtime-only walk finds no in-file function in bisect at all. The model
   calls what the file defines; CPython answers with what the import left
   bound. Comparing those two IS the standing §2.5
   accelerator-equivalence obligation (docs/memory-model.md §import
   forms — "the model runs the pure fallback where CPython runs the C
   accelerator, and the assertion that nothing observable differs is
   DIFFERENTIALLY TESTED, never taken from the docs"). Library mode is the
   instrument that obligation was waiting for, and every agreeing bisect
   row is a row of its discharge against the real `_bisect`.
3. **The battery is BALANCED and SEEDED.** Doctests first (the module
   author's own claims), then type-driven inputs from a fixed pool, with
   the per-function seed `crc32("module.function")` — never `hash()`,
   which is salted per process. Candidates are probed and then selected
   alternating between calls that RETURN and calls that RAISE: an
   unannotated signature makes most generated tuples type-incoherent, and
   an unbalanced battery is eight TypeErrors and no evidence about the
   value path. `--determinism` runs the survey twice and compares the
   battery BYTES.
4. **UNCOMPARABLE is a first-class answer, never agreement.** The
   typed-call protocol carries a VALUE and an exception CLASS and nothing
   else, so three things it cannot adjudicate are counted apart: a CPython
   answer outside the canonical value set, a call that PRINTED, and a call
   that MUTATED its arguments (deep-compared against a copy taken before
   it). Counting those as matches is exactly the silent agreement this
   project exists not to produce.
5. **Skipped is counted.** A function whose name matches the unsafe-verb
   list, or whose signature is `*args`/`**kw`/keyword-only (not drivable
   through a positional protocol), is reported as skipped and its module
   can never read as VERIFIED on a battery that quietly omitted it.

### The corpus manifest — 197 modules, both provenances

`harness/library_corpus.json`, generated by `--build-manifest` from the
committed censuses. Every row carries file, provenance, the census's wall
SET and its first-wall PREDICTION, so the scoreboard reconciles row by row.

* **141 from the census** (`docs/class-tier-census.json` `library`, the
  pure-Python modules in the seeds' import-time closures). Predicted
  first wall: `class-creation` 89, `import` 39, `none` 11, `node:*` 2.
  93 of them are C-reaching by the import-ceiling census's own rows; 48
  are not seeds there, so their closure is unrecorded.
* **56 in-repo** — the "import but no way to run" set, decided
  statically: at least one public top-level `def`, no top-level `print`,
  and no `__main__` guard, so running the file as a program compares
  empty stdout against empty stdout. 54 `Examples/python`, 1
  `harness/scripts`, 1 `vendor/cpython-3.9-lib-test`. That only 2 of 118
  in-repo non-Examples files qualify is itself the finding: the repo's
  scripts corpus is a PROGRAM corpus, and `Examples/python` is the
  library corpus that program mode has been scoring vacuously.

**RECONCILIATION NOTE, recorded before anyone re-derives it.** The census
JSON says **89** class-walled of 141; §THE CLASS-CREATION WALL says 87.
Both are right: 87 was measured BEFORE the third door closed, and §THE
THIRD DOOR CLOSED pre-registered exactly this move (`shlex` and
`sre_parse` from class-admitted to class-walled). The JSON was regenerated
after that landing. The manifest uses the JSON, so its prediction column is
the post-third-door one.

### THE BASELINE SCOREBOARD — MEASURED (2026-08-16, the L1 "before")

197 modules, 3526 battery calls, CPython 3.9.19 both ends, model at
`a1044ea`. This is the number the module system (L2) and the class tier
(L3) get measured against.

| verdict | all | census 141 | in-repo 56 |
| --- | --- | --- | --- |
| VERIFIED | 12 | 0 | 12 |
| BODY-ONLY | 8 | 8 | 0 |
| PARTIAL | 40 | 1 | 39 |
| REFUSED | 134 | 131 | 3 |
| DIVERGED | 2 | 1 | 1 |
| INCOMPLETE | 1 | 0 | 1 |

Per CALL, over the 3526 rows: **MATCH 2349, REFUSED 1124, DIVERGE 22,
UNCOMPARABLE 22, RUNNER 7, TIMEOUT 2.** Every one of the 22
UNCOMPARABLE rows is the same protocol gap — the call PRINTED and
`--batch` reports no stdout — which makes the hook request below a
measured number rather than an opinion.

**The headline of the shape: the stdlib half VERIFIES NOTHING.** Zero of
141. Not one pure-Python library module can today have its public
functions checked, because 131 of them refuse before the body finishes
and the 8 that do get through have no drivable public function at all.
Every VERIFIED row is in-repo. That is the honest "before", and it is
what makes the L2/L3 numbers meaningful: they are being asked to move a
count that starts at zero.

The refusal walls, by the construct the model itself named:
`class-creation` 91, `import` 34, then singletons —
`try/except uses unsupported features` 2, and one each of the ordering
admission (`locale`), heap-typed `+` (`__future__`), an unmodelled
builtin `frozenset` (`keyword`), `.extend` (`unittest`),
`node:Constant:bytes` (`quopri`), `node:DictComp` (`token`), `node:Set`
(`hashlib`).

### The census reconciliation: 179 EXACT, 2 ORDER, 16 UNPREDICTED

The class tier's prediction lands EXACTLY: the census says 89 of the 141
are class-walled, and **89 refused at `class-creation`** — plus the 2
in-repo class-walled files, for the 91 above. The two ORDER rows
(`hashlib` predicted `import`, fired `node:Set`; `quopri` predicted
`import`, fired `node:Constant:bytes`) are admission order inside the
census's own wall set, not census errors.

The 16 UNPREDICTED are TWO findings, and neither is a census mistake:

1. **Ten rows are the whole-file/import-time distinction** (`chunk`,
   `email`, and eight `Examples` files): the census's wall set is a
   property of the FILE, and the predicted wall sits inside a function
   body, which importing the module never executes. Checked, not
   assumed: recomputing those wall sets with the current extractor
   reproduces them exactly, so this is not census staleness. The walls
   are real and they resurface — in the CALL phase, as per-call
   refusals. A one-phase instrument could not have told these apart.
2. **Six rows are wall KINDS a static node census cannot see**
   (`__future__`, `_compat_pickle`, `copyreg`, `keyword`, `locale`,
   `unittest`): a heap-typed operator, an unmodelled builtin, a method
   outside the tier, `runScript`'s ordering admission, and two
   try/except shapes. The static census ranks NODES; these are dynamic
   values and Script.lean admissions. Worth recording because every
   ladder ranking to date has been computed from the static wall set.

### THE TWO DIVERGED ROWS — the stop-and-report headline

**1. `stat` — the §2.5 accelerator-equivalence obligation is FALSE, 21
of 104 calls.** The guarded-import arm admits `stat` on the argument
that running the pure fallback is observationally equal to CPython
running the C accelerator (docs/memory-model.md §import forms: "the
assertion that nothing observable differs is DIFFERENTIALLY TESTED,
never taken from the docs"). It is now differentially tested, on the
real module, and it fails: C `_stat` converts its argument to an
unsigned int, so `S_IFMT(-1)` raises `OverflowError: can't convert
negative value to unsigned int` and `S_ISDOOR('a')` raises `TypeError:
an integer is required`, while the pure fallback answers 61440 and
False. `S_ISDOOR`/`S_ISPORT`/`S_ISWHT` are literally `return False` in
3.9, so they accept anything at all. THE MODEL IS FAITHFUL TO THE FILE
IT WAS GIVEN; what is false is the admission's equivalence claim, on the
negative-int and non-int domains. Note `stat` is one of the eight stdlib
sweep MATCHes — program mode cannot see this, because the module prints
nothing either way.

The same test PASSES for `bisect`, the other C-accelerated module that
got a battery: 15 of 15 comparable calls agree, 0 diverge (the rest are
loud refusals at `<` across mixed types and the designed, unbuilt
`list.insert`). So the obligation holds for one and fails for the other,
which is exactly why it had to be measured.

**2. `arith.mod` — `str % list` answers TypeError where CPython returns
the string.** `"  x  " % [1, 3, 5]` is `'  x  '` under CPython 3.9 and a
`TypeError` under the model; `"abc" % [1]` is `'abc'` and likewise
refused-as-raised. A list satisfies `PyMapping_Check`, so `%` takes the
MAPPING path, and the mapping path does not run the "not all arguments
converted" check that the tuple path runs. Confirmed by hand at the
runner, independently of the harness. This is a WRONG ANSWER in the
recently landed `%` tier, not a refusal, and it is in-repo — an
`Examples` file the typed-call battery already covers, which no existing
row exercises with a non-tuple right operand.

### What the sweep taught about ITS OWN instrument

Five defects, each found by the run and fixed before the number above
was taken. Recorded because they are the failure modes any battery over
a real corpus will hit:

1. **Module state accumulated across battery calls.** The oracle
   imported once and drove the whole battery against one live module, so
   `list_lab.bump_twice()` answered 3 on the model (fresh world, `TABLE
   = [1,2,3]`) and 4 under CPython (earlier rows had already bumped it),
   and the harness reported a DIVERGED THAT WAS ITS OWN. Battery calls
   now re-execute the module body per call, which is what
   `callFunction`'s fresh world actually means — and it makes the
   battery order-independent, a stronger property than the seed alone.
2. **FUEL IS A DEPTH BOUND, NOT A TIME BOUND.** `fib(30)` at fuel 10000
   returns 832040: ~2.7M calls at depth 30 never approach the limit. So
   `fib(100)` — an ordinary row of the generated battery — runs
   effectively forever and never times out. With one batch for the whole
   corpus it ate the watchdog and took 239 later calls down with it. The
   call phase now runs ONE RUNNER PROCESS PER MODULE with a wall-clock
   bound, so a runaway costs its own module a loud INCOMPLETE. `fib` is
   the single INCOMPLETE row above, and it is the honest verdict.
3. **A cyclic value killed the oracle subprocess** and cost its module a
   verdict: canonicalization is now depth-capped, since a self-reference
   hits the recursion limit long before the node budget.
4. **Watchdog casualties were scored PARTIAL** — which reads as "the
   model answered and some answers were wrong" when the calls never ran.
   They now get their own INCOMPLETE verdict, a loud banner, and a
   nonzero exit.
5. **Concurrent chunks shared one jobs-file path** in the envelope
   cache, so one chunk could overwrite the jobs another chunk's runner
   was about to read — and the call phase pairs results POSITIONALLY, so
   a same-length cross would mispair silently. The path is now keyed by
   PID. (The same fixed-name pattern is in `harness/leanpy_survey.py`'s
   `survey-jobs.jsonl`; not this lane's file, and harmless while nothing
   runs two surveys at once.)

### How the baseline was collected, so it reproduces

The corpus is surveyed in six DISJOINT chunks selected by `--only`
(the stdlib path, `Examples/python` split `[a-f]`/`[g-o]`/`[p-s]`/
`[t-z]`, and the scripts/vendor pair), merged by `--merge`, which
refuses overlapping chunks by name rather than double-counting a module.
Chunking is not cosmetic: a single process surveying all 197 was stopped
twice by the environment before finishing, and the chunks run in
parallel in minutes.

DETERMINISM: the whole corpus was surveyed TWICE and the battery — every
module, function, argument tuple and its provenance (doctest or
generated) — compared byte for byte. **315666 bytes, sha256 `5c94d723c94de3be…`, IDENTICAL** — and all 197
module verdicts were stable across the two passes as well. Nothing in
the battery reads the wall clock, `hash()` (salted per process) or set
iteration order; the per-function seed is `crc32("module.function")`.

### Recorded hook requests (owned files this lane did not touch)

`Main.lean`'s typed-call protocol (`--batch`) carries neither the
exception MESSAGE (`--script-batch` does, as `exnmsg`), nor stdout, nor
the post-call world. Those three are the whole content of the
UNCOMPARABLE bucket: with `exnmsg` the call phase would compare messages
at the same tier the body phase already does, and with a post-call heap
the mutating half of the stdlib (`insort`, every in-place sort) would
become comparable instead of merely counted. Not this lane's file, and
each is a one-line addition to an existing JSON writer.

### Phase plan — SUPERSEDED by measurement, and by this instrument

The L1 entry proposed L2 (the module system) and L3 (the class tier v0) as
the next two phases. Both have since been PRICED WITH THIS SURVEY and the
answers are recorded in their own sections: §L2 CENSUSED AND STOPPED (the
`__name__` half is worth ZERO modules — the `import-semantics:__name__`
gate has never fired, in any run) and §L3 CENSUS-FIRST (cost unchanged,
value 1 and not 16). Read those, not the two bullets this section used to
carry. The library metric was built to say what a tier is worth before it
is built; on its first two customers it said "less than you think," twice.

## THE OBSERVATION HOOKS, WIRED — UNCOMPARABLE goes to zero (2026-08-16)

`--batch --observations` (§THE BATCH OBSERVATION HOOKS) landed on the
runner and this is the harness half: the flag on the CALL-phase
invocation, and the two early returns in `compare_call` replaced by real
comparisons — stdout against `lean_stdout(model)`, mutation against
`model.get("mutated")` with `args_after` compared when both sides mutated.
The oracle now records `args_after` in the runner's own encoding so the
two mutations are compared and not merely both noticed.

### The wiring delta, ISOLATED — exactly what was predicted

Attributing honestly needs the two halves separated, because the model
lane also moved the tree underneath. So the OLD comparison logic was
replayed offline over the SAME rows of the SAME run — every call row
stores both sides, so this is exact and needs no second sweep:

| per call, one run, one commit | old logic | new logic |
| --- | --- | --- |
| MATCH | 2297 | **2319** |
| REFUSED | 1120 | 1120 |
| UNCOMPARABLE | **22** | **0** |
| RUNNER | 7 | 7 |
| TIMEOUT | 2 | 2 |
| DIVERGE | 0 | 0 |

**One movement, 22 rows, all of it UNCOMPARABLE → MATCH** — the model
lane's replay predicted 22/22 and 22/22 is what happened. Nothing else
moved by a single row. Module-side, that is `fnprint` and `g1_lab`
PARTIAL → VERIFIED (8 printing rows each; `assert_lab`'s 6 rows clear too
but it keeps other refusals).

### The baseline, re-measured at `deddff7`

| verdict | L1 (474ee31) | now | why it moved |
| --- | --- | --- | --- |
| VERIFIED | 12 | **14** | +`fnprint`, +`g1_lab` — THE WIRING |
| BODY-ONLY | 8 | 7 | −`opcode` (upstream) |
| PARTIAL | 40 | 39 | −2 wiring, +`arith` (upstream) |
| REFUSED | 134 | **136** | +`stat`, +`opcode` (upstream) |
| DIVERGED | **2** | **0** | BOTH FIXED UPSTREAM |
| INCOMPLETE | 1 | 1 | `fib`, unchanged |

Calls 3526 → 3448: `stat` contributes 104 fewer (it refuses before the
call phase now) and `str_lab` 26 more (the starred-displays landing added
functions to the file). Both accounted for; no other module's count moved.

### BOTH L1 DIVERGED ROWS ARE CLOSED, and neither by this lane

* `arith.mod` — `293dd09 str % <mapping>: CPython skips the leftover
  check, and now so do we`. The row is MATCH; `mod("  x  ", [1,3,5])` now
  answers the string on both sides.
* `stat` — `724390d The §2.5 admission becomes a REGISTRY: 24 assertions,
  one ever checked`. The accelerator-equivalence assertion is no longer
  assumed per module; `stat` REFUSES with the named construct
  `ImportFrom:accelerator-diverges`, and `opcode` moved to REFUSED with
  it. A wrong answer became a loud refusal, which is the outcome the
  finding was reported for.

That is the library metric doing the job it was built for: two silent
divergences found by driving public functions, both closed at the layer
that owned them, and the scoreboard now reads DIVERGED 0.

### THE MESSAGE-TEXT SURFACE — measured, NOT promoted, and here is why

`--observations` also carries `exnmsg` on the call phase, so the message
tier the BODY phase applies became available to `compare_call`. It was
wired, measured, and then DELIBERATELY BACKED OUT: comparing message text
turns **169 call rows into DIVERGE, across 27 distinct text pairs**, every
one of them a `TypeError` whose CLASS already agrees. Promoting wording
drift into the survey's headline verdict would cost DIVERGED its meaning —
it is this instrument's word for a wrong VALUE or a wrong CLASS. The
number is kept here instead, because it is a real fidelity surface and
some of it is not wording at all:

| rows | model | CPython 3.9 |
| --- | --- | --- |
| 44 | `unsupported operand type(s) for +: 'str' and 'int'` | `can only concatenate str (not "int") to str` |
| 38 | same shape, `'list' and 'int'` | `can only concatenate list (not "int") to list` |
| 13 | `unhashable type: 'tuple'` | `unhashable type: 'list'` |
| 8 | `clear() takes no arguments (1 given)` | `dict.clear() takes no arguments (1 given)` |
| 8 | `Counter.bump() got multiple values…` | `bump() got multiple values…` |
| 8 | `Move() takes 3 positional arguments but 1 were given` | `<lambda>() missing 2 required positional arguments: 'j' and 'prom'` |
| 12 | `list indices must be integers, not X` | `list indices must be integers or slices, not X` |
| 9 | `range() arguments must be integers` | `'X' object cannot be interpreted as an integer` |

**Three of these are not drift, they are wrong facts.** `unhashable type:
'tuple'` NAMES THE WRONG TYPE where CPython names `'list'`; the `Move()`
row reports a different function and a different error shape; and
`range()` reports the wrong subject. The rest split into two systematic
families — CPython's concatenation-specific text for `+` on `str`/`list`
(82 rows, the bulk), and a qualifier convention the model gets backwards
in both directions (`dict.clear` under-qualified, `Counter.bump`
over-qualified). RECORDED AS THE NEXT DECISION, not taken here: a message
tier for the call phase wants its own verdict bucket (the body phase's
SAME/DRIFT/ABSENT vocabulary already exists), and the 13 wrong-type rows
want fixing whatever is decided about the other 156.

DETERMINISM, re-run after the wiring: the corpus surveyed twice, batteries
compared byte for byte — **310567 bytes, sha256 `3b131927ed7b…`,
IDENTICAL**, all 197 module verdicts stable.

## `py_vcgen` walks `for` — BUILT (2026-08-15)

The cross-cutting gap carried since the 2026-08-09 stop point ("`py_vcgen`
cannot walk `for` loops") is closed, in both layers.

**Layer 2 (VC2.lean) — the rule.** `for` is the while rule MINUS the
measure: `execFor` captures the iterated values BEFORE the loop begins, so
the invariant is indexed by the REMAINING elements and termination is
structural. `execFor_of_invariant` is the engine (induction on the element
list, the body's `brk`/`ret`/`err` escapes routed to `Q`'s arms exactly as
the while engine routes them), `PyStmtTriple.forLoop`/`PyTriple.forLoop`
the triple forms, `IterVals` the iterable's value-sequence dispatch
(`.listV`/`.tuple`/`.ntuple`/`str` — the immutable sources, where a
snapshot IS the live semantics). The elements are SPEC-side behind a
marshalling `elt : α → RVal`, which is what lets an invariant over a
boundary int list be written over `List Int` instead of `List RVal` with an
injectivity side condition at every step; `elt := id` recovers the raw
form, and `forLoopInt` is the int instance the walker drives. The `.ref`
arm (H2's live index cursor) and the generator arm are deliberately absent:
different recursion points, different observational story, and a rule that
quietly covered them would claim a snapshot semantics the interpreter does
not have.

**Layer 3 (VCTactic.lean) — the walker.** `handleFor` reads the element
list off the iterable's captured value at the entry state, builds the
remainder-indexed invariant, applies the rule through `consequence`,
discharges `hv`/`hiter`/`hexit`, walks the body once per element and
continues from the primed exit state. Three surface consequences, all
loud:

* a `for` consumes an `inv` clause but NO `dec` — `dec` clauses are now
  indexed by `while` rank (`VCCtx.decIndex`), so a `for`-free function
  keeps its exact positional pairing and the `invs.size == decs.size`
  check is relaxed to `decs.size ≤ invs.size`;
* the `inv`'s FIRST binder is the remaining-element list
  (`fun (rest : List Int) (best : Int) => …`; delayed form `case inv1`
  with `rest` in the context), the rest are Python names as before;
* a `break`-carrying `for` REQUIRES its `exit` clause. The while rule
  silently weakens to the bare invariant there; that is not repeated,
  because "the invariant at the empty remainder" is not the exit fact
  after a break.

The loop TARGET is bound by the loop itself and lives behind the symbolic
environment tail like any body-created variable — no hand-unrolled first
iteration. `for … else` has no rule at all (the interpreter refuses it).
The walker's v1 reads the iterable as a boundary/value LIST whose elements
are marshalled (`xs.map elt`) or int literals; heap lists, generators,
`str` and `range` refuse loudly and want the layer-2 rule by hand.

Acceptance: the walker's own smoke tests gained four `for` cases, all
SYMBOLIC (every int list, not one) — a whole-list fold, the same fold in
`break`-carrying fail-soft form (sunfish's `bound` loop in miniature), and
that one again in delayed-clause form, plus six `#py_check` runs. Every
existing `py_vcgen` proof (`tri`, `gcd`, `nested_flow`, `rsa_inverse`,
`bench_bisect`) is unchanged and green.

**What did NOT collapse, and why — the next gap, measured.**
`Examples/python/sf_bound_for`'s hand proof (130 lines: a `pw`/`E`
geometry, AST literals, a `key` list induction, a hand-unrolled first
iteration) was rewritten as a five-line `py_vcgen` call and it FAILS —
not on anything `for`-shaped, but on `best = max(best, score)`: a BUILTIN
call inside a loop body makes the interpreter check whether a local
shadows the name, and `Env.lookup tl "max"` against the invariant's
symbolic tail is stuck. That is the same gap `sf_bound_loop.py` already
records for `len` in a while test ("the builtin lookup consults the loop's
symbolic env tail and the test gets stuck"), now confirmed to block the
`for` path identically, so the hand proof stays. The fix has a shape: the
invariant shape must carry, per builtin the body calls, the fact
`Env.lookup tl "<name>" = none` — true at entry (`tl := []`, closes by
`rfl`) and preserved across iterations (the tail only ever grows by
`Env.set tl "<target>" v`, and `Env.lookup_set_ne` steps past it). Doing
that turns sf_bound_for, sf_bound_loop and sf_bound_rec into walker
one-liners, and it is the single highest-value next step for this tactic.

## The `arrVal_getElem` family, promoted (2026-08-15)

F-6 is closed: the family that lived copied in three example proofs is one
shared set of lemmas now (VCTactic.lean §marshalled-list indexing, beside
the other spec-side residual helpers `envInt`/`Env.lookup_set_*`).

The content is one lemma — mapping over an IN-RANGE `getElem?` and
defaulting is the map applied at the element, `map_getElem?_getD`, false
unbounded — plus the `getD`/`getElem` bridge in the orientation residuals
want, and the two `RVal` instances the symbolic runs actually leave
behind (`arrVal_getElem`, `getElem` form; `arrVal_getD`, `getD` form).

Call sites: `sf_bound_rec` and `bench_bisect` deleted their copies
outright (the shared signatures are the ones they already called; bisect's
two `arrVal` uses moved to the `getD`-form name), and `bench_statistics`
keeps a one-line local instance because its marshalling is `RVal.int`
applied directly with an `Option.getD` right-hand side — the local
statement is its own, the PROOF is the shared lemma.

This feeds the gen_moves work: the reference enumeration indexes a board
list at computed offsets, so every ray step meets exactly this shape.

## The gen_moves theorem — STATEMENT landed, proof not (2026-08-15)

`Examples/python/sunfish/genmoves_theorem.lean` states the decided
theorem. Both halves of the equality already existed and are already
CPython-checked (pins_genmoves.lean: the model's `Position.gen_moves` runs
on the opening, promotion and castling boards; `Ref.refMoves` is pinned on
the opening board plus thirteen adversarial ones), so what was missing was
the claim that ties them — and it is now written down exactly:

    GenMovesEqRef : Prop :=
      ∀ b score wc0 wc1 bc0 bc1 ep kp rf ms,
        Ref.refMoves b.toList wc0 wc1 ep kp rf = .ok ms →
        ∃ t, ∀ F ≥ t, genMovesOf F (posOf …) = some (refTriples ms)

Two things are load-bearing in that shape. The reference's answer is a
HYPOTHESIS, not a conclusion: the reference declines (`Except.error`) on a
board it cannot read and on an exhausted ray budget, so board
well-formedness lives there and nowhere else, and no `.error` can be
mistaken for a short move list. And the fuel is a THRESHOLD, the
total-correctness shape of every other judgment in the repo.

It is a `Prop`-valued DEFINITION, not a `sorry`ed theorem: this repo does
not land `sorry`, and a definition records the claim exactly while leaving
"proved" unclaimed. `theorem gen_moves_eq_ref : GenMovesEqRef` is the one
line to add when the proof lands; the statement does not move.

Proved alongside it: the presentation lemmas the decomposition will use
(`refTriples` distributes over `++` and `flatten`, since the reference is
built by flattening per-square and per-ray lists while the model arrives
one yielded move at a time).

NOT proved, and named precisely in the file: (1) ray agreement — the
model's generator resumed inside one `for j in count(i + d, d)` yields
exactly `Ref.ray`'s list, which is where the work is (six yield sites at
three control-flow depths, `yield from` for the promotions) and which
wants `Ref.ray`'s fuel monotonicity as a companion; (2) square agreement
by `directions[p]` order, including the kernel-computable six-key
agreement between the shipped dict and `Ref.directions`; (3) board
agreement for the outer `enumerate` scan with its `continue` arm. The
ray-monotonicity lemma was attempted and abandoned rather than landed
half-done — its `do`-block over `Except` wants `Except.bind_eq_ok`-style
decomposition, not a `cases` chain, and the file says so.

## `str % <mapping>` — the baseline's wrong answer, CLOSED (2026-08-16)

Divergence triage, item 1 of 2. The L1 baseline's `arith.mod` row was a
LIVE WRONG ANSWER in the freshly landed `%` tier: `'  x  ' % [1, 3, 5]`
is `'  x  '` under CPython 3.9.19 and was a `TypeError` under the model.
Design and measurement: docs/memory-model.md §`%`-formatting on strings,
"the mapping right operand".

**The mechanism, from the C source and not from the docs.**
`PyUnicode_Format` sets `ctx.dict = args` when
`PyMapping_Check(args) && !PyTuple_Check(args) && !PyUnicode_Check(args)`,
and the trailing leftover check is guarded `argidx < arglen && !ctx.dict`.
So a mapping right operand SUPPRESSES `not all arguments converted`
entirely. `PyMapping_Check` is `tp_as_mapping->mp_subscript ≠ NULL`,
measured through `ctypes.pythonapi` on the pin rather than read off a
doc page: **true for str, tuple, list, dict, range, bytes, bytearray;
false for None, bool, int, float, set.** str and tuple are then struck
out by the two `!` clauses, so inside this tier the mapping RHS is
exactly `listV` and `rangeV`.

**The fix is one predicate and one flag.** `strFormatMappingRhs`, and a
`Bool` threaded into `strFormatWalk` that its base case consults. What
did NOT change is the more interesting half: the positional state was
already right, because `arglen = -1, argidx = -2` means the first
conversion gets the WHOLE object and the second is `not enough
arguments` — which is exactly what the one-element list `[rhs]` already
did (`'%s' % [1,2]` → `'[1, 2]'`, `'%s %s' % [1,2]` → not enough
arguments). And `%(key)s`, the other half of `ctx.dict`, stays LOUD, so
the fix cannot open a path to a guessed answer.

RECORDED ASYMMETRY, pinned as `fmt_dict_leftover`: `'abc' % {'k': 1}` is
`'abc'` under CPython and LOUD here — `evalBinOp`'s heap-operand refusal
fires before the arm. A declared gap, not a wrong answer. And a REVISIT
marker: `listV` is the transitional value-semantics list, so when lists
move to the heap at H2 this predicate moves with them.

Battery: 21 new differential cases over five new `str_lab` functions
(`fmt_bare_leftover` carries BOTH sides of the predicate in one row —
list/empty-list answer, int/str/None/bool/tuple still raise) plus the
`arith.mod` row the baseline found it on, and eleven `#py_check`/`#guard`
pins in `str_lab/spec.lean`.

MEASURED: `lake build` 3660 jobs green; docs_check 67/67; diff_test
**1215 → 1236 cases, 0 failed**; script corpus 63 scripts 0 failed
(49 matched, 14 loud-blocked); in-repo survey 102/127, 0 DIVERGE. The
library baseline's `arith` row goes **DIVERGED → PARTIAL 43/48** (the
five are loud refusals on generated argument types, not answers).

## THE §2.5 ADMISSION BECOMES A REGISTRY — and two admissions are withdrawn (2026-08-16)

Divergence triage, item 2 of 2 — and the finding is bigger than the row
that produced it. The baseline's `stat` DIVERGED row was never a model
bug: "THE MODEL IS FAITHFUL TO THE FILE IT WAS GIVEN; what is false is
the admission's equivalence claim." So the ADMISSION is what got fixed.
Design and evidence: docs/memory-model.md §import forms →
"per-module differential admission"; the registry itself is
`ACCELERATOR_ADMISSIONS` in `extractors/python/extract.py`.

### The census that reframes it: 24 assertions, ONE ever checked

A guarded `from <C module> import …` of a platform-PRESENT module is the
one import form where CPython succeeds and the model does not: the
model's Pass 0 raises, the guard catches, and the PURE FALLBACK runs
where CPython ran C. Admitting that continuation ASSERTS observational
equivalence of the two branches, and the memo's own words
(docs/c-intrinsics-proposal.md §2.5) are that the assertion "is not taken
from the docs … any divergence — a message, a type, an edge case — is a
blocker, not a footnote."

Measured over the 197-module library corpus: **24 distinct accelerators
in ~30 files sit in guard position on a platform-present module.**
`_abc`, `_bisect`, `_codecs`, `_collections`, `_datetime`, `_decimal`,
`_functools`, `_hashlib`, `_heapq`, `_io`, `_locale`, `_opcode`,
`_operator`, `_pickle`, `_sha512`, `_ssl`, `_stat`, `_thread`,
`_warnings`, `binascii`, `collections`, `grp`, `pwd`, `zipimport`.
Exactly ONE of them had ever been differentially driven. Library mode
drove a second and it failed. The census is the point: the design named
four files and the corpus has twenty-four, so this was never a
four-entry footnote.

### The registry

Guard position is now NECESSARY AND NOT SUFFICIENT. An accelerator is
admitted only with a recorded measurement that PASSED, cited in the entry
beside the fallback it was measured on. No entry, no admission, and the
refusal says WHICH failure it is — so the census can tell "nobody looked"
from "we looked and it is wrong":

| py_kind | meaning | count in the corpus |
| --- | --- | --- |
| `ImportFrom:accelerator-unmeasured` | no entry — never driven | 22 accelerators; 2 modules reach it |
| `ImportFrom:accelerator-diverges` | an entry measured FALSE | 2 accelerators, 2 modules |

* **`_bisect` ADMITTED** — 15/15 comparable calls agree, 0 diverge
  (library mode, this baseline). The rest of that battery is loud
  refusals, never silent agreement.
* **`_stat` REFUSED, measured** — 21 of 104 calls. C `_stat` converts to
  an unsigned int, so `S_IFMT(-1)` raises `OverflowError` and
  `S_ISDOOR('a')` raises `TypeError` where the pure fallback answers
  61440 and False.
* **`_opcode` REFUSED, by inspection** — the branches differ in the NAMES
  they bind: CPython binds `stack_effect` and appends it to `__all__`,
  the `pass` handler binds neither. docs/memory-model.md already called
  this "the recorded §2.5 divergence, unseen because `__all__` is never
  printed", and *unseen* is not *equivalent*.
* the other 21, `binascii` included, are unmeasured. `quopri`'s is a
  genuine pure-accel fallback that may well pass; nobody has driven it,
  because `quopri` walls on `Constant:bytes` first.

### THE COST, stated first because it is a headline regression

**`opcode.py`'s program-mode MATCH — the `%` landing's flip — is
WITHDRAWN, and so is `stat`'s.** Stdlib sweep, measured BOTH WAYS with
the same binary (the extractor swapped between runs, 167 laptop seeds at
3.9.19): **8 MATCH / 159 REFUSE → 6 MATCH / 161 REFUSE, flip set exactly
{`opcode`, `stat`}** — the two withdrawn admissions and nothing else.

Both were matches on EMPTY STDOUT over a module namespace that differs.
`stat` proves that is not a technicality: the same untested assertion
produced 21 wrong answers the moment an instrument could see them, and
program mode called it a MATCH throughout. The module system (L2) is
exactly the work that makes those namespaces observable.

ONE LINE of the registry reverses either withdrawal if the owner would
rather keep the flip. That reversibility is deliberate: the price of the
doctrine is visible and payable in a single edit, rather than buried in
a predicate.

### THE BASELINE, RE-RUN — and DIVERGED is ZERO

Both triage items measured together, same six-chunk `--only`/`--merge`
protocol as the L1 baseline, CPython 3.9.19 both ends.

| verdict | L1 baseline | after triage | Δ |
| --- | --- | --- | --- |
| VERIFIED | 12 | 12 | — |
| BODY-ONLY | 8 | 7 | −1 |
| PARTIAL | 40 | 41 | +1 |
| REFUSED | 134 | 136 | +2 |
| **DIVERGED** | **2** | **0** | **−2** |
| INCOMPLETE | 1 | 1 | — |

Per call, 3526 → 3448 rows: **MATCH 2349 → 2297, REFUSED 1124 → 1120,
DIVERGE 22 → 0**, UNCOMPARABLE 22, RUNNER 7, TIMEOUT 2 all unchanged.
The call-count drop is stat's 104-row battery leaving; `str_lab` gains 26
for its five new public functions (derived from the three measured
totals, and every other module's battery is row-identical).

Every module that moved, and there are no others: `arith`
DIVERGED → PARTIAL 43/48 (the `%` fix); `stat` DIVERGED → REFUSED;
`opcode` BODY-ONLY → REFUSED; `abc` and `decimal` keep verdict REFUSED
and change WALL from `import` to `accelerator-unmeasured`.

Walls: `class-creation` 91 (unchanged — the class tier's number is
untouched), `import` 34 → 32, `accelerator-unmeasured` 2,
`accelerator-diverges` 2, the seven singletons unchanged.

**THE GOAL IS MET: zero standing DIVERGED rows.** Each of the two became
what it should have been — one a fix, one a named, evidenced gap.

Gate: extractor units 74/74 (four new registry rows); ZERO envelope
content changed in-repo (all 197 committed envelopes re-extracted and
diffed — the only deltas were the known `frontend.version` stamp, reverted
unstaged), because `_bisect` is the sole platform-present accelerator any
in-repo file guards and it stays admitted; docs_check 67/67; diff_test
1236 cases 0 failed; script corpus 63 scripts 0 failed; in-repo survey
102/127 with 0 DIVERGE.

### What this does NOT do

It does not model a single C accelerator, and it does not claim the 22
unmeasured ones diverge. It claims only that nobody has looked, and it
stops the model from ACTING as though someone had. Adding an entry is a
measurement, not an argument: drive the module through
`harness/library_survey.py` — its CALLS phase runs the model's fallback
against CPython's C accelerator, which is what makes it the instrument
this obligation was waiting for — record numerator and denominator, cite
the run.

## L2 — THE MODULE SYSTEM: CENSUSED AND STOPPED, with the shape recorded (2026-08-16)

The phase plan's L2 is two halves that library mode can now price
separately, and they price very differently. Neither number was known
before this instrument existed; both are measured below, against the
post-triage baseline (197 modules, DIVERGED 0).

### Half one — `__name__` import semantics. MEASURED WORTH: ZERO.

The recorded item: bind `__name__` to the module name so the survey's
`import-semantics:__name__` gate stops firing and
`if __name__ == "__main__":` becomes statically dead.

**The gate has never fired.** Not in the L1 baseline (whose refusal
walls are `class-creation` 91, `import` 34, seven singletons and two
try/except shapes — no gate row) and not in the post-triage re-run. It
fires only where the model would otherwise have claimed a body match,
and no module both gets a body run to completion AND reads `__name__`.

Of the 32 `import`-walled modules, **5 read `__name__` at top level**
(`base64`, `signal`, `site`, `sysconfig`, `uu`) and 4 of those carry a
`__main__` guard — and every one of the five walls on something else
first (`Constant:bytes`, `Lambda`, `Starred`, `Set`, `Constant:bytes`).
So the change flips ZERO modules today. Its cost is a `Script.lean`
binding mode, a `Main.lean` protocol field, a survey change, a battery
script and a full rebuild. Building it now would be paying a rebuild for
a number that is measured zero — §THE SEQUENCING PRINCIPLE, applied to
this lane's own work. It becomes worth building the moment half two
does, and not before.

### Half two — the import wall itself. MEASURED WORTH: 10 module bodies, and OWNER-GATED.

32 modules refuse at an import statement. The census asks the only
question that matters: **if every import were granted for free, and
`__main__` blocks were dead, where would the body stop next?**

| next wall | modules |
| --- | --- |
| (none statically) | 11 |
| `Constant:bytes` | 6 |
| `With` | 4 |
| `Set` | 3 |
| `Import` / `ImportFrom` (a second, non-admitted form) | 3 |
| `Starred` / `Starred:target` | 2 |
| `Lambda`, `JoinedStr:conversion_r`, `UnaryOp:Invert` | 1 each |

"Granted for free" cannot mean EXECUTED. §The IMPORT CEILING measured
0 of 155 seeds with a pure-Python import closure, and that has not
moved: of the eleven above, every census row with a recorded closure is
C-reaching. The only shape available is the OPAQUE MODULE VALUE
(docs/memory-model.md §The FUTURE modeled-module arm) — bind the name
to a value every observation refuses on.

An opaque value only helps if the top level never OBSERVES it, so the
eleven were checked one by one (function and class bodies excluded —
importing never runs them):

* **8 never touch an imported name at top level**: `collections.abc`,
  `contextvars`, `email.base64mime`, `email.charset`,
  `importlib.machinery`, `reprlib`, `rsa_inverse`, `struct`.
* **2 touch only BENIGN-whitelist names the model already models** —
  `fnmatch` (`itertools.count`), `unittest.util`
  (`collections.namedtuple`) — so they are clean too.
* **1 genuinely observes**: `xml.parsers.expat`, line 7,
  `sys.modules['xml.parsers.expat.model'] = model`.

**So the opaque-module arm is worth TEN module bodies of 197** — they
stop being REFUSED and become BODY-ONLY/PARTIAL/VERIFIED candidates,
with the battery deciding which. That is the first honest number this
idea has ever had, and it is the library metric the phase plan said was
"where its value was always claimed to be".

### THE STOP, and why it is a stop and not a slow-down

The arm that pays is OWNER-GATED — docs/memory-model.md says so in its
own words ("This arm is OWNER-GATED with the rest of the memo and is
recorded here only so the Pass 0 constructor is not built in a shape
that forecloses it"), and it is not small: a new `RVal` constructor
means a loud arm at EVERY observation site (every operator, every
builtin, attribute read, call, `print`, `==`, `is`, truthiness,
rendering, the boundary freeze), which is the widest kind of edit this
model has. The arm that is ungated flips zero.

RECOMMENDED, in order:

1. **Take the ten to the owner as the ask.** The question is no longer
   "should there be a module system" — the import ceiling answered that,
   NO. It is the narrower "should a from-import bind an opaque value
   nothing may observe", and the answer is worth 10 module bodies plus
   the retirement of a refusal class.
2. If the answer is yes, `__name__` rides the same rebuild — it is a
   few lines and it stops being a zero the moment bodies run.
3. The 21 blocked-behind are a BATCH, not a ladder, and the biggest
   single member is `Constant:bytes` at 6. §THE SEQUENCING PRINCIPLE
   applies verbatim; nothing in that list is worth pricing alone.

INSTRUMENTS: the two censuses are
`/scratchpad`-local scripts derived from `harness/library_corpus.json` +
the extractor's own `convert_stmt` (ground truth is never
re-implemented, the `class_census.py` discipline). Reproduce by walking
each module's top level, skipping `Import`/`ImportFrom` and
`__name__`-guarded `if`s, and reporting the first `Unsupported` node or
`creation_effects` class.

## L3 — THE CLASS TIER v0: CENSUS-FIRST, and the VALUE moved (2026-08-16)

The GO was granted on library-mode approval, and the census-first
discipline says re-verify the design's claims against current HEAD before
writing a line — the design (2026-08-14) predates the depth landings, and
one of them touched `worldInv`'s neighbourhood. Done, both halves. **The
COST is unchanged to the digit. The VALUE is not, and the instrument that
moved it is the one the GO was granted on.**

### The COST claims, re-verified at the statements (all HOLD)

| design claim | measured at HEAD |
| --- | --- |
| `fuelMono` 18 conjuncts | **18** (17 `∧`, Obs.lean:410) |
| `worldInv` 11 conjuncts | **11** (10 `∧`, Obs.lean:1999) |
| `clockErase`'s `CE` 18 conjuncts | **18** (17 `∧`, ClockErase.lean:652) |
| `worldInv` VACUOUS on the tier | **holds** — `Module.heapFree` still conjoins `m.classes.toList.isEmpty` (Semantics.lean:3894) |
| 17 `Stmt.pass` match sites, 7/8/2 | **17** — 7 Semantics.lean, 8 Json.lean, 2 Script.lean; the other `.pass` occurrences in Json.lean are CONSTRUCTIONS, not enumerating matches, and VC.lean's is a triple rule, not a match |
| `Stmt` gains one constructor | 19 → **20** |
| Script.lean carries no meta-theorem | **0** `theorem`/`lemma` in 891 lines |

The two depth landings moved none of it: 46ce995 (`while … else`) touched
Script.lean, which no theorem quantifies over, and b1e31c1 (`heapFree`
past `.get`) touched Obs.lean and Semantics.lean without adding a
conjunct. So the 700–1000-line estimate over five files stands, and so do
the three build-cost poles.

ONE DRIFT FOUND AND FIXED on the way past: `Module.heapFree`'s projection
docstring said "The three conjuncts" of what is a FOUR-way `&&` (pass 3's
`topLevelDefFree` made it four, and four projection theorems sit under
that comment). Model-matches-code, corrected in place.

### The VALUE claim, MEASURED for the first time — and it is 1, not 16

§THE CLASS-CREATION WALL's recommendation 2 says v0 "is built for the
library batch (87 of 141 pure-Python modules are class-walled)", and the
phase plan says "library mode is the first instrument that can collect
it". Library mode has now collected it, and CLEARING A WALL IS NOT
RUNNING A MODULE:

* v0 (the instrument's own `V0` set, T1+T2+T3+T4) clears **16 of the 89**
  class-walled library files — the design's number, reproduced exactly.
* **ZERO of those 16 have no other wall.** Every single one re-walls on
  `import`. Three (`code`, `string`, `unittest.main`) have `import` as
  their ONLY remaining wall; the other thirteen have two to eight more
  (`Starred` 9, `Delete` 5, `Global` 5, `With` 4, `Set` 3, …).
* And it is not the whole-file/import-time confusion the L1 baseline
  caught: the check was redone in SOURCE ORDER, admitting the class
  statement and asking what the first top-level `Unsupported` is.
  **16 of 16: `Import` 15, `ImportFrom` 1** — `import sys`,
  `import select`, `import fnmatch`, `import _string`, … every one of
  them a module-body statement the survey really reaches.
* In-repo, `cls_lab` DOES flip: its only demand is
  `base:same-module-class` and its `other_walls` is empty (censused
  directly, controls 20/20 + 0 ground-truth violations). The OTHER
  in-repo class-walled row, `seq_tests`, does not: it demands
  `base:builtin-type` and `base:dotted`, both outside v0, so it stays
  class-walled — which is what makes the arithmetic below exact.

**So L3 v0 built ALONE moves the library metric by exactly ONE module.**
Pre-registered, before any code:

* wall census `class-creation` **91 → 74** (16 census clears + `cls_lab`);
  `import` **32 → 48**. A wall RENAME for 16 of the 17.
* module verdicts: **one** row improves — `cls_lab`, REFUSED →
  BODY-ONLY/PARTIAL/VERIFIED as its battery decides. VERIFIED 12 → 12
  or 13. Everything else in the table is unchanged.
* program mode, unchanged from the design's own pre-registration: stdlib
  flip set EMPTY, in-repo **+2 MATCH** (`cls_lab.py` and
  `cls_effect_script.py` — the file that PINS the class-creation
  refusal; that arc closes and the pin moves to the new boundary).

### THE ORDERING, which is the actual product of this census

Put beside §L2 — THE MODULE SYSTEM, measured the same night on the same
corpus:

| built | library-mode module bodies unlocked |
| --- | --- |
| L3 v0 alone | **1** (`cls_lab`) |
| L2's opaque-module arm alone | **10** |
| L2 then L3 v0 | 10 + 1 + the 3 import-only clears = **~14** |

§The IMPORT CEILING wrote the sentence in 2026-08-13 — "every bit of that
value is BEHIND a module system, because these are modules nothing
imports today" — and §THE CLASS-CREATION WALL repeated it. Neither could
put a number on it. **The numbers are 1 and 10, and they say the two
phases are in the wrong order.**

### STOPPED, and what to do instead

Not built. The GO was granted on a library number, and the library
instrument has now refuted that number for this ordering; building 700–
1000 lines of Lean for one in-repo module would be exactly the grinding
the census-first rule exists to prevent.

1. **Take L2's opaque-module arm to the owner as one decision with this.**
   It is the strictly larger number AND the unlock for L3's. The ask is
   narrow: should a from-import bind an opaque value nothing may observe?
2. **If the owner says yes, build L2 then L3 v0** — in that order, and
   the class tier's pre-registration becomes ~4 library modules instead
   of 1, on top of its language value.
3. **If the owner says no, L3 v0 is still legitimate — but on the LANGUAGE
   argument, not the library one.** §THE CLASS-CREATION WALL's
   recommendation 2 names it: "inheritance is the biggest remaining hole
   in the class model and `CallsIn` over an inheriting class is a theorem
   shape this project does not have." That is a real reason. It is not a
   number, and it should be chosen as itself.
4. The SOUNDNESS half of this lane is already done and stays done: the
   third door closed on 2026-08-14, and the census re-confirms it
   (0 creation-pure classes running a decorator, "anything but 0 is a
   REGRESSION").

## The builtin-lookup gap is closed — and sf_bound_for collapses (2026-08-16)

The fix recorded yesterday as "the single highest-value next step for this
tactic" is built, and it is exactly the shape that was predicted: a loop
invariant now carries, per name the loop CALLS, the fact

    Env.lookup tl "<callee>" = none

(`mkTailFreeFact`, appended to the invariant's conjunct chain by
`appendConj` so the user's own conjuncts keep their `hinv1`/`hinv2`
positions). Callee names come from `calleeNames`, a plain structural walk
of the AST literal for `Expr.call (Expr.name f)` nodes at any depth;
names the loop assigns, and names already in the literal environment
prefix, are filtered out — the first because the fact would not be
preserved, the second because the lookup never reaches the tail.

Why it was needed: the interpreter checks for a local shadowing a builtin
before calling it, and against an invariant's symbolic tail that check
reduces past every literal entry and then stops dead. Why it is free: the
fact is true at loop entry (`tl := []`, closes by `rfl` in the `init`
shape-solve) and preserved across an iteration (the tail only grows by
`Env.set tl "<target>" v`, and `Env.lookup_set_ne` — already in the
walker's rewrite set — steps past it), so both obligations discharge
inside the walker and neither reaches the user. Both loop rules get it,
`while` and `for`, and the post-loop midcondition carries it too, so the
continuation after the loop can call builtins as well.

**Payoff, measured.** `Examples/python/sf_bound_for/proof.lean` — sunfish's
fail-soft beta-cutoff loop, the step-2 milestone — went from 149 lines to
47: a `pw`/`E` environment geometry, `loopTgt`/`loopBody` AST literals, a
`key` list induction in fuel-threshold form and a main theorem that
hand-unrolled the first iteration are all gone, replaced by a nine-line
`py_vcgen` call with an `inv` and an `exit` clause and `grind
[sfSearchMoves]` on the three residuals. The hand proof stays in git
history at df7eba7.

**The other two did NOT fall, and the reason is worth having.**
`sf_bound_loop` (the index-`while` twin) is still blocked, but by ONE gap
now instead of two: `scores[i]` in the loop body captures as
`(Option.map (RVal.thaw ∘ ToVal.toVal) scores[i.toNat]?).getD RVal.none`
and reducing it needs `i.toNat < scores.length` — which the invariant and
the loop test DO supply, but only to an arithmetic discharger, and
`captureRun`'s simp has none. The fix is a discharger on captured runs
(`simp (disch := omega)`, the spelling this gallery's hand proofs already
use) with the shared `arrVal_getElem` family as the landing shape. It
touches EVERY capture in the walker, so it wants its own pass and its own
regression run rather than a ride-along. `sf_bound_rec` reads the same
subscript and waits on the same fix (plus the recursion path, which the
call rule already supports). The blocked file's header records this.

## gen_moves, ray leg: the budget lemma ATTACKED (2026-08-16)

Not proved, and therefore not claimed — but no longer unexplored. The
worked map is in `Examples/python/sunfish/genmoves_theorem.lean`; the two
findings worth having outside it:

1. **The missing primitive.** Nothing in core's simp set decomposes a
   successful `do`-block over `Except`. `(x >>= g) = .ok c ↔ ∃ a, x = .ok a
   ∧ g a = .ok c` (by `cases x <;> simp [bind, Except.bind]`) is the lemma
   every tactic on `Ref.ray` stalls without, and with it `split at h` walks
   the guards and the `Option` match fine (`Ref.A1`/`Ref.H1` need
   unfolding, or the two castling branches leave `Ref.H1 = Ref.A1`
   standing).
2. **The wrong turn, recorded because it looks right.** Casing on the
   recursive call and refuting the `.error` branch does NOT work: a ray
   that breaks on its first guard returns `[]` without forcing the tail, so
   `body(.error e) = .ok []` is satisfiable. The tail is consumed on
   exactly one leaf; every other leaf is independent of it — which is also
   the shape the eventual ray-AGREEMENT proof has to exploit, since the
   model's generator consumes its ray step the same way.

The recommended next move is (b) in the file: factor the body as
`rayBody … (tail)` with `ray … (f+1) j = rayBody … j (ray … f (j+d))` by
`rfl`, prove once that `rayBody` is map-or-constant in its tail, and take
both the budget lemma and the ray-agreement induction off that one
characterization. Square agreement (`directions[p]`, six kernel-computable
keys) and the `enumerate`-scan board leg are untouched and unchanged.

## The captured-run arithmetic pass — and sf_bound_loop falls (2026-08-16)

The follow-up named in the previous entry is built. It turned out to be
two mechanisms, not one, and the difference is the finding:

* **A DISCHARGER** (`captureDischarge`) — simp's default first, then
  `omega` over the accessible facts — for the hypotheses of conditional
  rewrites. This is what lets the shared `arrVal_getElem` family fire: the
  marshalled subscript read is a conditional rewrite whose in-range side
  condition the loop invariant supplies.
* **SIMPROCS** (`decideArith`, keyed on `<`/`≤`/`∧`) for the interpreter's
  own guards. A discharger is NEVER consulted about an `ite` CONDITION,
  and a subscript's range check `if (0 ≤ k) ∧ (k < ↑len) then some … else
  none` is exactly that. Anyone who reaches for `simp (disch := omega)`
  here and stops will watch it change nothing; the arithmetic has to be
  IN the simp set, not beside it.

Three implementation facts that cost real time and are worth not paying
twice:

1. `Omega.omega facts g` proves `False` from facts — it is not
   goal-directed. Called on the goal directly it silently proves nothing
   ("a possible counterexample may satisfy …" while the goal is not even
   in the constraint set). The tactic's own shape — `falseOrByContra`
   first, then every local hypothesis — is what works (`omegaProve`).
2. A `simproc_decl` pattern written `(_ < _)` elaborates at the DEFAULT
   numeric type, `Nat`, and then never matches an `Int` comparison. The
   patterns are ascribed per type here.
3. `getLocalHyps` returns value locals (`i : Int`) as well as proofs, and
   omega chokes on them; filter by `isProp`.

**Scope, measured rather than guessed.** The pass touches every capture,
and two existing proofs said so: `nested_flow` broke because the walker
became STRONGER (residuals it used to hand back were now closed, so the
proof script's `⟨…⟩`s no longer matched), and `rsa_inverse` blew its simp
step budget. Both are fixed without touching either proof: the simprocs
are gated on a LENGTH mention (`isIndexGuard`), which keeps them on
subscripts and off a loop measure's `Int.toNat`; and the exec context's
step budget is raised to 1e6, a walker-internal limit that a longer — not
looping — rewrite cascade legitimately needs (`rsa_inverse` elaborates in
36s).

**Payoff.** `Examples/python/sf_bound_loop` — blocked since the day it was
written, the file that NAMED these gaps — is a live `py_vcgen` proof now.
What the walker leaves is only mathematics: peel one element off the
scanned suffix (`List.drop_eq_getElem_cons`), or none at all past the end,
and `searchMoves` steps.

**`sf_bound_rec` did NOT fall, and not for an arithmetic reason.** Its
recursive call is `return bound_rec(scores, gamma, i + 1, b)` — a call in
RETURN position, and the walker's v1 recipe takes calls only as the whole
right-hand side of an assignment. Tested, not assumed: with the IH in
context and every subscript now reducing, the walk gets to the `return`
and stops there. The leg it needs is a new walker case, and layer 2
already has the primitive — VC2.lean's `EvalsTo.call` docstring names
`return f(x)` as its splice point. That is a separate pass with a separate
regression, so it is recorded rather than started.

## Calls in return position — and the third bound proof falls (2026-08-16)

`return f(…)` is a walker case now, and with it `sf_bound_rec` joins
`sf_bound_for` and `sf_bound_loop`: all three transliterations of
sunfish's fail-soft cutoff loop are `py_vcgen` calls, certified against
the same `sfSearchMoves` constant from `formal/Sunfish/Bound.lean`.

**The rule is not call-shaped.** `PyStmtTriple.retExpr` (VC2.lean) is
stated over an arbitrary expression — `return e` with `e` evaluating to
`v` lands in `Q.ret` at `v` — because the call-specific half is
`EvalsTo.call`, whose own docstring already named `return f(x)` as a
splice point. Layer 3 shares the whole front half of a call site between
the assignment case and the return case (`buildCallEvalsTo`): shadowing
checks, argument evaluation, callee-fact lookup, `EvalsTo.call`. The two
handlers differ only in what they do with the result, which is exactly
the division the primitive predicted.

**Two things the recursion needed that the tooling did not have.**

1. **Quantified local facts.** `findCalleeFact` matched a local hypothesis
   only when its type was a ground `CallsTo`. A recursion IH is
   `∀ b, f(…, b) ==> …`, because the branch that reaches the call binds
   its own `b`. Local hypotheses now go through the same
   `forallMetaTelescope` instantiation the `@[py_spec]` registry always
   used, with leftover `Prop` obligations kept as `side` goals; a ground
   fact is just the empty telescope.
2. **Marshalled list arguments do not match definitionally.** The captured
   run holds `map (thaw ∘ toVal) l` while a spec's boundary args thaw to
   `thawList (map toVal l)`, and bridging those is an induction
   (`thawList_eq_map`), not an unfolding — so `isDefEq` refused every fact
   about a list-taking callee, which is every recursion over a boundary
   list. `checkArgs` compares normal forms when the direct check fails.

**And one that was not tooling at all, recorded because it cost the most
time here.** `omega` does not see a hypothesis OR a goal whose type is
`PyInt` — the abbreviation survives in the elaborated term and omega's
matcher is syntactic on `Int`/`Nat`. This is why the gallery writes
`(i : Int)` ascriptions everywhere; now the reason is written down. The
`sf_bound_rec` induction states its bound at `Int` (`↑scores.length ≤
i + n`, subtraction-free — Nat subtraction under a `toNat` is the other
shape omega drops) and restates `0 ≤ i` at `Int` before using it.

Sizes, for the record: sf_bound_for 149 → 47, sf_bound_loop blocked → 66,
sf_bound_rec 153 → 119 (it keeps the model constant, the exit lemma and
the induction skeleton; what left is the four hand-written branch
combinations and their `py_simp` runs). The hand proofs are in history at
df7eba7 and before.

## The ray leg, factored — and where the flagship actually stops (2026-08-16)

The recorded plan worked exactly as recorded, which is the good news, and
it also measured the bad news precisely.

**Landed, in `Examples/python/sunfish/genmoves_theorem.lean`:**

* `exceptBind_ok` / `exceptMap_ok` — inversion of a successful `do`-block
  over `Except`. Core's simp set has no equivalent, and every tactic on
  `Ref.ray` stalls at the first `←` without it.
* `rayBody` — the ray's body with the recursive call abstracted as a
  parameter, transcribed verbatim, so `ray_step` (`ray … (f+1) j =
  rayBody … j (ray … f (j+d))`) holds by `rfl`.
* `rayBody_map_or_const` — **the characterization**: every leaf either
  ignores the tail or maps ONE fixed function over it. The whole proof is
  `unfold; simp only [bind, Except.bind]; repeat' split` and then each
  leaf by `rfl` on one side of the disjunction. This is the same fact the
  earlier wrong turn stumbled over (an early `break` never forces the
  tail, so refuting the `.error` branch is unprovable) — going THROUGH it
  turns the obstacle into the tool.
* `ray_mono` / `ray_at_least` — the budget lemma, three lines off the
  characterization. The reference's step budget is now provably an
  artifact of writing it in Lean, not part of what `GenMovesEqRef` claims.

**Ray AGREEMENT does not land, and the reason is tooling, not effort.**
Stating it is fine: a suspended `gen_moves` is a `GenCont` frame stack
whose shape inside a ray is concrete (`block … :: countFrom j d :: … ::
enumSeq <board> :: []`). **[CORRECTED 2026-08-17, §L4 PARTIAL: that stack
is WRONG in two of its frames — `count`/`enumerate` allocate their own
generator objects and the ray is a `forGen` frame over one. The shape was
recalled here, not measured; §L4 prints the measured one.]** Proving it is
not, because the statement
quantifies over an ARBITRARY board: every `self.board[j]` is a subscript
on a symbolic 120-char string and every guard is a comparison on a
symbolic character, so nothing reduces and the interpreter would have to
be case-split by hand at every step. That is precisely what `py_vcgen`
does for the heap-free fragment — and there is no generator case in the
walker, no triple layer over `stepIter`/`execGen`, and (checked) no
generator-level lemmas in the repo beyond `stepIter_mono` and clock
erasure.

So the flagship's remaining distance is a `PyGenTriple` layer (yield sites
as postcondition arms, the frame stack as the state), a walker case that
consumes it, and symbolic string/char reasoning for the guards. The same
wall stands in front of the square-agreement and board-scan legs — both
also quantify over an arbitrary board — which is why none of the three was
attempted piecemeal. `GenMovesEqRef` stays a definition.

What this session did close is the target: the reference side is a settled
object now — factored, characterized, budget-free — so the agreement proof
will meet a fixed target when the tooling exists.

## THE BATCH OBSERVATION HOOKS — `--batch --observations` (2026-08-16)

The library lane's recorded hook request (§LIBRARY MODE, "Recorded hook
requests"), and it arrived QUANTIFIED: **all 22 UNCOMPARABLE rows of the
L1 baseline are one gap** — "the call printed; `--batch` reports no
stdout". Contract: `Main.lean` header, "`--observations`"; and
docs/DESIGN.md.

### Why the fields were not there, and where they come from

`callFunction` is `Run.toPublic ∘ callIn ∘ thaw` over a fresh world, and
`Run.toPublic` ERASES the world — so the public result genuinely has
nothing else to give. Under the flag the batch driver unrolls the wrapper
one step, calls `callIn` itself, and keeps the world. That is the whole
mechanism; no semantics moved and `LeanModels/` is untouched.

| field | present exactly when |
| --- | --- |
| `stdout` | the run reached a world (`.ok`/`.exn`) — same shape and same `World.stdout` as `--script-batch`, so the survey's existing list-of-lines adapter reads it unchanged |
| `exnmsg` | the model's `PyErr` carries a message — `--script-batch`'s rule verbatim |
| `args_after`, `mutated` | the run reached a world AND every argument freezes; else `args_after_refused` says why |

`args_after` is DERIVED, never asserted, and the distinction is the
design: today a `Val.list` thaws to an IMMEDIATE `RVal.listV`, so a callee
cannot reach a caller's argument and `mutated` comes out false. That is
worth PRINTING rather than omitting — CPython's `insort` mutates, so the
two answers then DISAGREE instead of being counted unverified. When lists
move to the heap at H2 the same expression reads the real mutation with no
edit here.

### OPT-IN, and the reason is measured

Turning the fields on unconditionally **failed 1156 of 1271 diff_test
cases on the first run.** `harness/diff_test.py` compares the model's line
to a dict it builds itself by WHOLE-DICT equality (`cpy == lean`) — which
is exactly the strictness a differential wants, and exactly what an
"additive" key breaks. So the flag: without it the line is byte-identical
to what `resJson` always printed, and no existing consumer changes.
Recorded as a general rule: **on this runner, "additive" is not a safe
word — the result line is compared whole.**

### THE 22, REPLAYED — the proof, without touching the fenced harness

The survey's `compare_call` still returns UNCOMPARABLE on
`oracle.get("stdout")` whatever the model emits, so the baseline delta is
**ZERO BY CONSTRUCTION** until the harness lane wires the flag in. Rather
than promise the outcome, it was MEASURED: every UNCOMPARABLE row was
re-driven through `--batch --observations` and compared with the survey's
OWN adapter (`lean_stdout`, copied not edited) against the oracle's
captured stdout.

**22 of 22 become MATCH.** `assert_lab.lazy_fail`/`lazy_pass`/`talk` (6,
`'evaluated\n'` both sides, and the `exnmsg` `"boom"` agrees too),
`g1_lab.try_print` (8), `fnprint.shout` (8). Zero DIVERGE, zero residual
UNCOMPARABLE. The bucket is now a wiring step, not a protocol gap.

### Measured

Runner rebuilt and both modes diffed on the same jobs file (byte-identical
without the flag). `lake build` 3663 jobs green; docs_check 67/67;
diff_test **1271 cases, 0 failed**; script corpus 64 scripts, 0 failed;
in-repo survey 105/130, 0 DIVERGE; stdlib sweep 6/167 unchanged; library
baseline 197 modules, every module verdict and all 3448 call verdicts
IDENTICAL — the zero-delta this section predicted.

**HANDOFF, one line for the harness owner:** add `--observations` to the
CALL-phase runner invocation, then in `compare_call` replace the
`oracle.get("stdout")` early return with a comparison against
`lean_stdout(model)`, and the `oracle.get("mutated")` early return with a
comparison against `model.get("mutated")`. The `exnmsg` branch is the
body phase's, already written.

## THREE WRONG FACTS IN ERROR MESSAGES — FIXED, and a fourth found (2026-08-16)

§THE MESSAGE-TEXT SURFACE split its 27 text families into 156 rows of
systematic DRIFT and **three that are not drift but WRONG FACTS** — the
model stating something untrue about the program. Those three are closed.
Re-running that lane's own census against the fixed model:
**169 → 138 drifting rows.** The −31 is the three families (13 + 8 + 9)
plus one more the re-census exposed.

The systematic 156 are untouched and stay with the call-phase
message-tier decision.

### 1. `unhashable type` named the KEY, not the offender (13 rows)

`{(1, [2]): 0}` answered `unhashable type: 'tuple'`; CPython 3.9.19 says
`'list'`. `tuple.__hash__` hashes its ELEMENTS, and the first one to
raise is the one whose message escapes. `unhashableName?` now mirrors
`hashableKey`'s recursion arm for arm and reports the first failing
member, depth-first left to right; `keyRefusal` names it. Pinned in
`dict_lab` on the store path, the read path and a doubly-nested tuple.

### 2. The arity `TypeError` had ONE shape where CPython has TWO (8 rows)

`Move(i)` answered `Move() takes 3 positional arguments but 1 were
given`. CPython says `<lambda>() missing 2 required positional
arguments: 'j' and 'prom'` — wrong callee, wrong shape, wrong counts,
and a grammar error too.

This was a KNOWN simplification, recorded at `arityOk`: "CPython's
message wording differs per case … but the harness compares exception
class names, so one canonical message serves both". The message tier is
what turned that shortcut into a wrong fact. One builder now, measured
live in every graduation:

* too MANY is the TAKES form — `takes 1 positional argument` singular,
  `but 1 was given` singular INDEPENDENTLY, and a defaulted callee is
  `takes from L to N positional arguments` (plural even at `from 0 to 1`).
* too FEW is the MISSING form, listing the parameters the call never
  reached, with the Oxford comma from three names on (`'i', 'j', and
  'prom'`; verified to five).
* a NAMEDTUPLE's `__new__` is an eval'd LAMBDA whose first parameter is
  `_cls`, so the callee is `<lambda>` and both counts are one higher
  than the field count. Once that is said, the generic builder produces
  CPython's text exactly.

Wired at all five sites (`callIn`, `callClosure`, `mergeKwArgs`, and
both namedtuple constructions). `fillKwSlots` came with it: it raised
per-parameter, so `def g(a,b,c)` called `g(a=1)` named only `'b'` where
CPython names `'b' and 'c'` — a census pass now collects every unfilled
name and raises once.

**THREE OF THE REPO'S OWN PINS HELD THE WRONG TEXT, and every one of them
failed the build** — the acceptance signal firing exactly where it
should: `Tests.lean`'s `clamp()` guard, `bench_statistics`' `median_low()`
row (whose text also carried the `1 positional arguments` plural bug), and
`sf_position`'s `bad_arity_raises` — in the SPEC and in the PROOF. All
re-measured against 3.9.19 and re-pinned.

### 3. `range()` named its own requirements, not the offender (9 rows)

The three-argument arm answered `range() arguments must be integers`,
which CPython 3.9 never says; the one- and two-argument arms were already
right. Now per-position, first bad argument left to right — verified
that CPython really is left-to-right (`range('a',[2],3)` is `'str'`,
`range([1],'b',3)` is `'list'`).

And through the HEAP: `range({1: 2})` is `'dict' object cannot be
interpreted as an integer`, where the pure `typeName` would have put the
`"object"` placeholder into a decided outcome — the recorded rule against
exactly that. `RVal.typeNameH` MOVED verbatim above the range block for
it (Lean has no forward references; the `%`-formatting landing's
precedent).

### 4. FOUND BY THE RE-CENSUS: `enumerate`'s start argument said `'str'`

Not on the lane's list, and only visible once the range family was
cleared: the start-argument arm had `'str'` **hard-coded**, so
`enumerate(['a','b'], [])` reported `'str'` where CPython says `'list'`.
One line, the same heap-resolved treatment, pinned over list/str/None
starts in `gen_lab`. A literal in a message position is the cheapest
possible wrong fact and the hardest to see.

### Measured

`lake build` 3663 jobs green; docs_check 67/67; diff_test **1271 → 1288
cases, 0 failed**; extractor units 74/74; script corpus 64 scripts, 0
failed; in-repo survey 105/130 with 0 DIVERGE; stdlib sweep 6/167 with 0
DIVERGE.

Library baseline, 197 modules: VERIFIED 14, BODY-ONLY 7, PARTIAL 39,
REFUSED 136, INCOMPLETE 1, **DIVERGED 0**; per call over 3476 rows MATCH
2347, REFUSED 1120, RUNNER 7, TIMEOUT 2, UNCOMPARABLE 0.
**ZERO verdict movement from these fixes**, as predicted — the survey
does not compare message text, which is exactly why these three could sit
wrong for so long. The evidence is the drift census, not the scoreboard.

### An instrument defect these runs exposed, recorded not fixed

Running the six library chunks CONCURRENTLY with the in-repo survey
produced a `RUNNER` verdict for `dict_lab`: *"is not a valid envelope:
offset 106380: unexpected end of input"*. The envelope cache
(`tools/leanpy`) is keyed by source hash and written NON-ATOMICALLY, so
two surveys that both need to (re)write the same entry can have one read
a half-written file. It only shows the first time a given source is
extracted, which is why adding functions to `dict_lab` surfaced it. Same
family as the recorded "concurrent chunks shared one jobs-file path"
finding, whose fix was to key the jobs file by PID; the cache write wants
temp-file-plus-rename. Re-running the chunk serially clears it, and the
baseline above was collected serially. Not this lane's file to fix.

## THE ENVELOPE CACHE'S WRITE BECOMES ATOMIC — the last shared-infrastructure race (2026-08-16)

The defect the previous section recorded but did not fix. `tools/leanpy`
`envelope_for` returns early on `os.path.exists(out)`, so **the final name
is a PUBLICATION**: the instant it exists, any concurrent survey reads it.
The extractor wrote straight to it, and `json.dump` on a buffered file
writes in chunks — so the entry was published empty and filled in
afterwards.

### The window, measured before anything was changed

A 26 MB envelope: the path **appears at +1.13s** and the dump runs to
**+2.01s**, growing through **554 distinct observed sizes**. Not a
theoretical interleaving — an 870 ms window in which the cache serves a
truncated file to anyone who asks. The casualty was real: a library sweep
scored `dict_lab` a `RUNNER` on
`is not a valid envelope: offset 106380: unexpected end of input`.

It surfaces only on a source's FIRST extraction, which is why it waited
for a run that added functions to `dict_lab` — every other sweep hit a
warm cache and took the early return legitimately.

### The fix

Extract to a unique temp IN THE SAME DIRECTORY, then `os.replace` it into
place. Same filesystem is what makes the rename atomic, so the entry
either does not exist or is whole. Two racers write two temps and both
rename: harmless, because the contents are equal BY CONSTRUCTION — the
cache key IS (source, extractor, frontend family), so last-writer-wins
cannot serve a different answer.

Two details that are not free choices. The temp still ends in `.json`,
because `extract.py` reads a non-`.json` `--out` as a DIRECTORY (found by
the test: the first attempt used `.tmp` and every extraction failed). And
it is a DOTFILE, so a `<stem>-*.json` scan of the cache cannot mistake a
temp for an entry. It is unlinked on every failure path — a stray temp is
litter; a stray entry would be served.

### The gate: the race is PROVOKED, not argued

`tools/test_leanpy.py` (new, wired into `tools/ci.sh` beside the extractor
tests), three tests:

1. **The race itself.** One process extracts a fresh 4000-function source;
   a second waits for the entry's final name to appear — which is exactly
   the condition the early return tests — and then does what a survey
   does: asks `envelope_for` and reads. Pinning the arrival instead of
   leaving it to luck is what makes it deterministic; the window it lands
   in is the real one. **BEFORE the fix it fails**, with
   `CORRUPT: Expecting property name enclosed in double quotes: line 1203
   column 8 (char 32726)` — a truncated envelope at a buffer boundary,
   the same failure class as the observed casualty. After, three rounds
   clean.
2. **The writer-level invariant, timing-free**: whatever path the
   extractor is told to write is NOT the path handed back, it IS in the
   same directory (or `os.replace` is not atomic), and it does not
   outlive the rename. Also fails before the fix.
3. **A failed extraction publishes nothing** — a syntax error must leave
   the cache empty, temp included.

### Measured

Both new tests fail on the old writer and pass on the new one, under 3.9
and under the 3.14 that `ci.sh` runs them with. `lake build` 3663 green;
docs_check 67/67; diff_test 1288 cases 0 failed; extractor units 74/74;
script corpus 64 scripts 0 failed; in-repo survey 105/130 and stdlib
sweep 6/167, both 0 DIVERGE.

**And the demonstration that matters: the six library chunks were re-run
IN PARALLEL with the in-repo survey against a DELETED cache** — every one
of the ~330 sources a first extraction, which is precisely the condition
that produced the corruption. Result: **zero corrupt-envelope rows, and a
scoreboard identical to the serial baseline** — VERIFIED 14, BODY-ONLY 7,
PARTIAL 39, REFUSED 136, INCOMPLETE 1, DIVERGED 0; 3476 calls, MATCH
2347, REFUSED 1120, RUNNER 7 (the known `fib` battery), TIMEOUT 2. No
module moved.

The concurrent-sweep protocol is safe again, which is what the six-chunk
baseline procedure depends on.

### One thing the cold-cache run exposed, reverted not fixed

Deleting the cache made `sum_to.py` re-extract for the first time in
weeks, and that dirtied `Examples/python/sum_to/SumTo.lean` — the
INLINE-mode companion, which is regenerated next to the SOURCE on every
extraction and records the path it was handed. Isolated: a RELATIVE path
regenerates it byte-identically, an ABSOLUTE one writes absolute
`source:`/`load_program` lines. So a survey that passes absolute paths
dirties the tree, and a warm cache hides it by never re-extracting.

Nothing to do with the atomic write (the companion is written beside the
source whatever `--out` says) — it is the recorded
`script_corpus.py dirties the tree` family, with the caller identified
now. Reverted here; the fix belongs with whoever owns the companion
write, and it is either "always relativise `source_path` against
`REPO_ROOT`" or "never regenerate a companion for an out-of-tree
extraction".

## THE COMPANION WRITE BECOMES PATH-INVARIANT — the dirty-tree family closes (2026-08-16)

The other half of the finding the atomic-cache section recorded. One
string, `rel_posix(source_path)`, is embedded in THREE places: the
envelope's `source_file`, the companion's `source:` header, and the
companion's `load_program … from "…"`. It was `normpath` of the path AS
GIVEN, so the same source extracted through a different spelling produced
different bytes.

That matters because an INLINE-mode source regenerates its committed
companion on every extraction. A survey passing an absolute path rewrote
`Examples/python/sum_to/SumTo.lean` with absolute `source:`/`load_program`
lines — and warm caches hid it, because the cache is keyed by source
BYTES and never re-extracts a known source. A second consequence, not
noticed until the key was written out: the cache could serve an
absolute-path envelope to a relative-path caller, with a `source_file`
neither would have written.

### The canonical form was READ, not chosen

`Examples/python/sum_to/SumTo.lean` says
`source: Examples/python/sum_to/sum_to.py` and
`load_program sum_to from "Examples/python/sum_to/sum_to.json"` —
**repo-relative POSIX**. So that is the rule, with the one honest
exception the corpus forces: a source OUTSIDE the repo has no
repo-relative form and keeps its absolute POSIX path, which is what every
cached stdlib envelope already carries and is already invariant. Both
arms go through `realpath` first, so the answer stops depending on the
caller's spelling or its CWD.

### The gate

Three tests in `tools/test_leanpy.py`, beside the cache-race ones,
driving the REAL committed example — "matches what is checked in" is the
property that keeps the tree clean, so a fixture would have tested the
wrong thing. They save and restore the two files in `setUp`/`tearDown`,
because a failing dirty-tree test must not leave a dirty tree.

1. **Four spellings agree, and agree with what is committed**: relative
   from the repo root, absolute, relative from `Examples/`, and absolute
   from an unrelated CWD — companion AND envelope byte-identical, and
   equal to the committed companion.
2. **The committed form is repo-relative POSIX**, asserted by reading the
   committed file, so the convention cannot drift silently into
   `rel_posix`'s idea of it.
3. **An out-of-tree source keeps an absolute REALPATH**, and two
   spellings of it agree.

**All three FAIL before the fix**, with exactly the reported divergence:
`source: /Users/ahle/repos/lean-surfaces/Examples/…` against
`source: Examples/python/sum_to/sum_to.py`.

One existing extractor unit test moved with it:
`test_normal_path_keeps_block_comment_header_verbatim` built its
expectation from the raw temp-dir path, and its fixture lives under a
`/var` that realpaths to `/private/var`. Its subject is the HEADER SHAPE,
so it now spells the path with `rel_posix` and says why; path invariance
has its own tests.

### Measured

74/74 extractor units; 6/6 in `tools/test_leanpy.py` under 3.9 and under
the 3.14 `ci.sh` uses; `lake build` 3663 green; docs_check 67/67;
diff_test 1288 cases 0 failed; script corpus 64 scripts 0 failed; in-repo
survey 105/130 and stdlib sweep 6/167, both 0 DIVERGE; library baseline
197 modules unchanged (VERIFIED 14 / BODY-ONLY 7 / PARTIAL 39 / REFUSED
136 / INCOMPLETE 1, DIVERGED 0; 3476 calls, no module moved).

**Every tracked envelope was re-extracted and diffed: ZERO content
change** — the committed corpus was already extracted with relative paths
from the repo root, which is exactly the form the canonicalisation now
guarantees. (The only deltas were the known `frontend.version` stamp,
reverted unstaged.)

And the direct proof: the cold-cache PARALLEL sweep — every source a
first extraction, the condition that dirtied the tree — now **leaves the
tree clean**. `SumTo.lean` does not appear in `git status` at all.
## The generator tier — DESIGN MEMO, awaiting a go (2026-08-16)

`docs/generator-tier-architecture.md` is the decision document for the
tooling that `GenMovesEqRef` is blocked behind. Nothing is implemented; the
memo exists so a go starts landing 1 instead of starting design. Censused
against the tree, and three things in it are worth surfacing here:

1. **One price is revised DOWN, with evidence.** The stop-and-report called
   symbolic string/char reasoning open-ended. It is not: every string
   operation `gen_moves` performs is already defined through
   `String.toList` (`strCharVals`, the `.str` arm of `indexVal`,
   `strContains` via `strFindAux`) — no `String.Pos`, no UTF-8 byte
   arithmetic on the path — and `Ref.at?` was already written over
   `List Char`. The missing set is 10–15 lemmas hanging off two mechanisms
   that already exist (the `arrVal_getElem` family and the captured-run
   simprocs/discharger). What IS true is that the Python layer contains
   zero string theorems today.
2. **The generator tier EXTENDS the VC stack rather than duplicating it.**
   `genPlan` splits every statement into `.delegate` (no yield → ordinary
   `execStmt`, already covered by layers 1–2) and five suspendable shapes.
   So the new layer is five constructors on top of the existing triples,
   and every yield-free statement inside a generator body is discharged by
   machinery that already ships.
3. **A drained generator is a value list, so the `for` rule already
   applies.** The `IterVals` exclusion of generators was right at the
   SEMANTICS level and stands; at the SPEC level, a `GenYields` fact hands
   the walker a finite element list and `execFor_of_invariant` applies
   verbatim. Laziness only bites when the consumer breaks, which is why the
   spec object has a prefix half (`GenYieldsPrefix`) — the half `bound`'s
   beta cutoff needs.

Plan: five landings, each gated and each collapsing something real —
L1 string bridge (0.5–1d, HIGH confidence) ∥ L2 `GenYields` + frame rules
(2–4d, MEDIUM; its gate is the FIRST generator theorem in the repo —
gen_lab has 73 differential rows and no `proof.lean`) → L3 walker case
(1–2d, MEDIUM-HIGH; gate collapses `sf_order`'s `bound_probe`, unlocking
the H6 ordering theorem) → L4 ray agreement (3–6d, LOW-MEDIUM — the band
that could double) → L5 square + board + assembly (2–4d, MEDIUM; gate is
`theorem gen_moves_eq_ref : GenMovesEqRef`). Total 9–17 working days.

## L1 LANDED — the string-as-list bridge (2026-08-16)

Landing 1 of docs/generator-tier-architecture.md, and only landing 1: L2–L5
(`GenYields`, the frame rules, any `PyGenTriple` work) stay owner-gated.
This family is ordinary depth tooling — it pays for any symbolic-string
proof in the repo, tier or no tier.

**What landed** (VCTactic.lean §strings as lists of characters, beside the
`arrVal_getElem` family it is modelled on): `normIndex_of_nonneg`,
`strLength_eq_toList`, `strIndex_ok` (the string subscript, in the shape
the interpreter leaves, with the in-range side condition stated over `i` so
the existing `omega` discharger proves it), `strFindAux_singleton_isSome`,
`strContains_singleton`, `ofList_singleton`, `strCharVals_eq_map`,
`valEq_singleton`. Ten declarations counting the gate's two — the memo
predicted 10–15.

**The gate** (`Examples/python/sunfish/genmoves_theorem.lean`):
`at?_eq_indexVal` — at any index the reference accepts, the model's
subscript reads the same character. Stated over an ARBITRARY board and an
arbitrary index, negative-index fold included, with two `#guard` pins on
the shipped opening board for non-vacuity. It is the first theorem in this
repo relating the reference enumeration to the interpreter, and it is the
shape a ray-agreement proof consumes at every square.

**Wiring, measured rather than assumed.** `strIndex_ok`,
`strContains_singleton` and `valEq_singleton` are in `interpLemmas`, so
captured runs use them — the full regression is green with them in
(3663 jobs), unlike the arithmetic pass, which needed gating. Nothing in
the gallery exercises them yet; they are in place for L4.

**Calibration data for the memo's other estimates** (the reason to record
it): L1 was estimated 0.5–1 day at HIGH confidence and took roughly two
hours, well inside the band. Three small tactic hiccups, all mechanical:
`simp [String.singleton]` loops (use `String.toList_singleton` and the
`toList_injective` route instead), `set` is not available in this
toolchain's tactic set, and `beq_eq_false_iff_ne` wants `.mpr` rather than
a simp rewrite. Nothing structural was wrong — which is the evidence that
the HIGH-confidence band on mechanical lemma families is real. It says
nothing about L4's LOW-MEDIUM band, which remains the one to watch.

## L2 LANDED — `GenYields` and the first generator theorem (2026-08-17)

Landing 2 of docs/generator-tier-architecture.md. L3–L5 (the walker case,
ray agreement, the assembly) stay owner-gated; nothing below touches the
walker or `py_vcgen`.

**The new file** is `LeanModels/Python/VCGen.lean` — "the generator tier
(`py_vcgen` layer 2G)", imported by `LeanModels/Python.lean` after VC2.
Before it the repo held exactly two facts about the generator tier
(`stepIter_mono`/`execGen_mono`, plus clock erasure) and no way to say what
a generator COMPUTES.

**The spec objects, as the memo decided them.** `GenYields m st k vs st'`
(the machine yields exactly `vs` and then finishes) and
`GenYieldsPrefix m st k vs st' k'` (the first `vs` values, machine left
suspended at `k'`), both in the repo's fuel-threshold idiom over the two
new spec-side drivers `drainGen`/`stepGenN`. Neither driver is in the
interpreter's mutual block — nothing in the interpreter calls them — so
they cost no `fuelMono`/`worldInv`/`clockErase` conjunct; their
monotonicity (`drainGen_le`/`drainGen_mono`, `stepGenN_le`/`stepGenN_mono`)
is proved here off `execGen_mono`.

**The design decision the memo did not make, and the one that mattered.**
Composition is list concatenation — the memo said so — but *what* composes
had to be chosen. It is **`GenEmits m st pre ws st₁`**: the frame PREFIX
`pre` emits `ws` and falls through, *for every continuation below it*.
Frame-stack polymorphism is the whole trick: the interpreter only ever
scrutinizes head frames, so every structural rule is stated over `pre ++ k`
with `k` universally quantified, and `GenEmits.trans` is literal
`List.append` on the frames and the output at once. Underneath sit two
threshold primitives: `GenSteps` (one decided resumption step) and
`GenSilent` (the machine rearranged its stack without yielding — with the
fuel offset existentially quantified, which is what makes silent
transitions compose transitively).

**The frame rules**, one per `GenFrame` kind, each holding at EVERY
continuation: `genSteps_nil`/`genYields_nil`, `genSilent_blockNil`,
`genSteps_yieldHere`, `genSilent_branch`, `genSilent_whileHere`,
`genSilent_whileTrue`/`genSilent_whileFalse`, `genSilent_forHere` (through
VC2's `IterVals` — the same value-sequence dispatch the statement-level
`for` rule uses), `genSilent_forSeqNil`/`genSilent_forSeqCons`,
`genSilent_enumSeqNil`/`genSteps_enumSeqCons`, `genSteps_countFrom`, the
live-cursor arms `genSilent_forListCons`/`genSilent_forListDone`/
`genSteps_enumListCons`/`genSilent_enumListDone`/`genSilent_forGenCons`/
`genSilent_forGenDone`, `genSilent_delegate` + `GenEmits.blockDelegate`
(the yield-free statements go through the layer-1/2 `PyStmtTriple`, so
statement semantics keeps exactly one definition) and
`genYields_blockReturn`. The sequence rule `GenEmits.forSeq` is
`execFor_of_invariant` with the output list threaded — remainder-indexed
invariant, structural induction, no measure — and the ray rule
`genYieldsPrefix_countFrom` says the only thing an infinite frame can say:
a prefix of every length, machine still there.

**The gate** — `Examples/python/gen_lab/proof.lean`, which did not exist
(73 differential rows, no proofs):

* `upto_yields` — **the first generator theorem in this repo.** `upto(n)`,
  suspended exactly as `callIn` leaves it, yields `0, 1, …, n-1` and then
  finishes. Symbolic in `n`, symbolic in the world, stated over the frame
  stack the interpreter actually builds.
* `naturals_prefix` — **laziness, as a theorem.** The INFINITE `naturals()`
  has no `GenYields` at all and yet hands over a prefix of every length,
  left in one fixed resumption configuration. An eager, list-producing
  representation of a generator could not state this.
* `upto5_yields`/`naturals4_prefix` — the `total(5)`/`first_over_inf` rows'
  generator content, as instances of the symbolic theorems (no interpreter
  run elaborated), plus two `#guard` non-vacuity pins running `drainGen`
  and `stepGenN` in the kernel.

**Two measurements worth keeping.**

1. *Stating a program's shape as one big existential over its source spans
   is a trap.* `∃ s₁ … s₁₂, uptoBody = [ … ] := ⟨_, …, rfl⟩` cost **5 min
   37 s** of elaboration by itself — twelve metavariables unified at once
   against a whnf of the 271 KB module literal. Projecting the pieces out
   one at a time (`uptoWhileS`, `uptoTest`, `uptoYield`, …) and pinning
   each with its own small existential is the same claim in **25 s**, and
   the theorem statements then mention the projections, so they say "the
   shipped `upto`" instead of "some program with these spans".
2. *The concrete rows were NOT promoted to theorems, deliberately.*
   `gen_lab.aliased(4) ==> 1` by `CallsTo.intro 4096 (by rfl)` blows past a
   million heartbeats. That is the boundary already recorded in
   `Examples/python/sunfish/pins_clock.lean` — `#guard`'s evaluator is
   untrusted and ~1000× faster than a checked reduction — so the identity
   rows stay `#py_check` pins at the trust level of the whole existing pin
   battery. The symbolic theorems are the better trade regardless:
   `upto_yields` covers every `n` and no concrete row does.

**What remains of L2, precisely.** The `drainIter` bridge over a WHOLE
drain. The per-step halves landed unconditional
(`stepIter_of_genSteps`/`stepIter_of_genDone`: a `GenSteps` fact about the
stored continuation IS the heap object's step, with both of `stepIter`'s
writes explicit), and they are what L3's walker case consumes. The whole
drain needs a heap-stability side condition — the body must not write slot
`a` itself, which `drainGen` threads no object and therefore cannot see —
and inventing its shape before a consumer needs it would be guessing.
Recorded rather than attempted, per the standing stop-condition.

**Calibration.** L2 was estimated 2–4 days at MEDIUM confidence and took
roughly one working session. The memo's stated risk (the live-cursor
frames) did not materialise at the per-step level — those rules are three
lines each with the heap read as a hypothesis; the risk is real one level
up, at the loop-invariant rule, which is exactly the piece deferred above.
The unforecast cost was elaborator performance on the module literal
(measurement 1), not the proofs.

## L3 LANDED (core) — the consumer side, and `total(n)` (2026-08-17)

Landing 3 of docs/generator-tier-architecture.md, **its rules and its
first consumer theorem**; the walker automation and the `bound_probe`
collapse the memo named as L3's gate did NOT land and are decomposed at
the end of this entry. L4–L5 stay owner-gated.

**What a consumer needed that L2 did not have.** L2 specifies a suspended
MACHINE — a frame stack and a frame state. A consumer never sees one: it
CALLS a generator function, gets a heap object, and steps it with a `for`.
The new file section is `LeanModels/Python/VCGen.lean` §"L3: the consumer
side", and it holds exactly three things plus their plumbing.

* **`IterSteps m w a r w'`** — one decided step of the generator OBJECT at
  `a`, the world-level twin of `GenSteps`. L2's two heap-object bridges
  are its introduction rules verbatim (`IterSteps.of_genSteps`/`of_genDone`
  are one-liners over them); `IterSteps.pureStep`/`pureDone` are the common
  case, where the resumption touches only its own frame, and `closed` is
  the drained object answering `none` forever. Three `Array` facts carry
  the heap bookkeeping: `Heap.get?_push_size`, `Heap.update_push_size`, and
  `Heap.update_update` (two writes to one slot are the second write — which
  is what makes `stepIter`'s enter-`.running`/exit-`.suspended` pair ONE
  observable change of the object).

* **`EvalsIn` and `EvalsIn.genCall`** — the memo called this
  `EvalsTo.genCall`, and that name cannot be right: `EvalsTo` is
  pinned-state by construction and a generator call ALLOCATES. `EvalsIn` is
  the stateful twin of `EvalsTo` exactly as `CallsIn` is `CallsTo`'s, and
  `EvalsIn.genCall` says a generator call is a `.ref` at the heap's end
  whose object is `genObj` — whose stored continuation is `[.block body]`,
  literally the frame stack every `GenYields` theorem is stated over. That
  is what makes "a generator is a value with a specification" true with no
  glue. Note there is no `heapFree` hypothesis and there could not be: a
  module with a generator def is not heap-free, which is precisely why
  `EvalsTo.call` cannot serve this position.

* **`execForGen_of_invariant` / `PyStmtTriple.forGen` / `PyTriple.forGen`**
  — `for x in <generator>` with the same remainder-indexed invariant the
  value-sequence `for` rule uses; the engine is `execFor_of_invariant` with
  one `stepIter` in front of each round. Deliberately not an `IterVals`
  constructor, so VC2.lean's exclusion note stands untouched.

**Two design questions the memo left open, and their answers.**

1. *The heap-stability side condition — L2's recorded remainder — is not
   needed here, and inventing one would have been wrong.* The loop rule
   does not assume the body leaves the generator alone: it demands a FRESH
   `IterSteps` fact at the state each round actually begins in, and the
   INVARIANT carries the object across the body. A body that clobbers the
   iterator slot cannot re-establish the invariant; one that leaves it
   alone re-establishes it for free. A `WritesAvoid`-style frame predicate
   would have been the special case dressed as a rule. **L2's remainder
   narrows**: the whole-drain `drainIter` bridge (`sorted(gen)`) still
   wants one, because a drain has no body in which to re-establish
   anything.

2. *The lazy half needs no second rule.* The memo budgeted
   `GenYieldsPrefix` at the consumer level for the `break` case. It is not
   needed, because **`Inv []` may be `False`**: a consumer that always
   escapes states an invariant unsatisfiable at the empty remainder, which
   discharges the exhaustion obligation vacuously and never asks the
   generator to finish. An infinite generator is consumed by the same rule.
   Supported, and stated in the file header — but see the remainder below:
   it is not yet EXERCISED by a theorem.

**The gate** — `Examples/python/gen_lab/proof.lean`, extended:

* `total_calls` — **`total(n) ==> 0 + 1 + ⋯ + (n−1)`, the first arrow-form
  spec in this repo for a function whose meaning runs through a
  generator.** Symbolic in `n`, over the shipped `total`. Every L3 object
  is on its path: the call allocates (`EvalsIn.genCall`), the loop steps
  (`PyStmtTriple.forGen`), the per-round obligations are `upto_iter` /
  `upto_iter_done`. `total5_calls` is the `total(5) = 10` differential row
  as an instance, with two `#guard` non-vacuity pins.
* Underneath it, `upto` as an OBJECT: `upto_first`, `upto_resume_step`,
  `upto_first_done`, `upto_resume_done` (machine level, from L2's frame
  rules) and `upto_iter`/`upto_iter_done` (object level). The worlds a
  generator loop passes through come out UNIFORM — `w.heap.push (uptoObj n
  k)` at every round, never a growing tower of `Array.set`s — which is what
  `Heap.update_push_size` buys and what made the invariant writable.

**What remains of L3, precisely.**

1. *The walker arm* (`classify` → `handleForGen`, the `GenYields`-fact
   lookup reusing `findCalleeFact`'s ∀-instantiating shape). Not attempted.
   It is a bigger chunk than the memo priced, and the census says why:
   `py_vcgen`'s whole call path goes through `EvalsTo.call`, which is
   gated on `m.heapFree = true` and therefore CANNOT fire in a module with
   a generator def. `handleForGen` needs its own front half over
   `EvalsIn.genCall`, not a reuse of `buildCallEvalsTo`'s. The rules above
   are what it would drive, and they are usable by hand today.
2. *The `bound_probe` collapse* (the memo's stated gate). Beyond L3 it
   needs, enumerated: the whole-drain `drainIter` bridge for
   `sorted((… for m in pos.gen_moves()))` — L2's remainder, still open with
   its heap-stability condition; generator-internal `break`, which unwinds
   the frame stack (`genBreak`) and therefore reaches BELOW `GenEmits`'
   polymorphic prefix, so it needs a loop-frame-level rule; the nested-def
   GENERATOR closure (`callClosure`'s generator arm — `EvalsIn.genCall` is
   the module-function arm only); and the ordering line itself, which is
   L4/L5. It was not a one-landing gate.
3. *An effectful ASSIGNMENT rule* — `g = upto(n)` as a statement.
   `EvalsIn.genCall` covers the iterable position of a `for`;
   `PyStmtTriple.assignName` takes an `EvalsTo` and so cannot bind a
   generator to a name. This is the one small piece between here and
   `gen_lab.two_phase`, which is the cheapest theorem that would EXERCISE
   the lazy half (a `break` abandoning the object, a second loop resuming
   it) — and exercising that half is the recorded gap in finding 2 above.

**Calibration.** L3 was estimated 1–2 days at MEDIUM-HIGH. The rules and
the gate took one working session, inside the band; the walker arm was not
attempted and its price is now measured rather than guessed (item 1). Two
elaboration traps, both the module literal again and both worth the record:
a `py_simp` over a statement that is still a PROJECTION (`uptoBump`) rather
than its pinned literal blows the 200 000-heartbeat budget — rewrite with
the `_lit` existential inside the `by` first, which is what L2's
proofs did at the top level and what this one had to do locally; and
`obtain rfl : k = N` eliminates the THEOREM BINDER `N`, not the local `k`
(`subst` prefers the right-hand variable), which silently deletes the name
the rest of the proof is written in.

## L3 TAIL LANDED — the effectful bind, `two_phase`, and the walker arm measured a second time (2026-08-17)

The remainder recorded at the end of §L3 LANDED (core), item by item: **item
3 is closed, and with it the "lazy half" gap of finding 2**; item 1 (the
walker arm) is not closed, and what it costs is now measured rather than
inferred — the first measurement named the smaller of its three blockers.
Item 2 (the `bound_probe` collapse) was out of scope here and is untouched.

**The effectful bind (item 3).** `PyStmtTriple.assignNameIn` /
`PyTriple.assignNameIn`, LeanModels/Python/VCGen.lean §L3 "Binding the
object to a name". `PyStmtTriple.assign`'s conclusion PINS the out-state's
world to the in-state's, so no instance of it can bind an allocation; the
twin takes an `EvalsIn` and stores into the world the call produced. Four
lines of proof — small, exactly as priced. Stated beside the pure rule
rather than replacing it: every heap-free assignment should keep using the
pure one.

**`gen_lab.two_phase` (the gap in finding 2).** `two_phase_calls` —
**`two_phase(n) ==> 1` for every `n ≥ 2`**, symbolically in `n`
(Examples/python/gen_lab/proof.lean), with `two_phase5_calls` as the
differential row's instance and a `#guard` non-vacuity pin. It is the first
theorem in the repo about a generator that is ABANDONED and then RESUMED,
and it EXERCISES the half §L3's finding 2 recorded as supported-but-untried:
both loops carry `Inv rest := rest = [k] ∧ st = …`, so `Inv []` is
`[] = [k] ∧ …` — a `False` that discharges `hexit` vacuously. Neither loop
ever asks `upto(n)` to finish. That is the same shape an INFINITE generator
would be consumed in, which is what makes the claim in VCGen.lean's section
header a demonstrated one rather than a design intention.

Two of the three claims gen_lab's own docstring names stop being rows
because of it: **`break` SUSPENDS**, and **a generator is heap IDENTITY** —
the second loop's `hiter` observes the SAME address in configuration 1
(`.suspended`, `uptoResume`), which is exactly why `b = 1` and not `0`. The
old note said identity would stay a `#py_check` row because promoting a
CONCRETE run costs a checked kernel reduction this interpreter cannot
afford; that measurement still holds, and the symbolic route sidesteps it
rather than contradicting it.

Cost: one session, no surprises. The two elaboration traps §L3 recorded were
both avoided by following the record — project-and-pin every statement
literal before any `py_simp`, and never `obtain rfl` against a pattern whose
right-hand side is a theorem binder. First time that entry paid for itself.

**The walker arm (item 1): three blockers, not one.** §L3 recorded the
first. Probing `py_vcgen [gen_lab]` on `total(5) ==> 10` — a two-line
scratch file, not a guess — surfaced the other two, and they change the
shape of the work.

1. *(recorded)* `py_vcgen`'s call path is `EvalsTo.call`, gated on
   `m.heapFree = true`, which cannot hold in a module with a generator def.
   `handleForGen` needs its own front half over `EvalsIn.genCall`.
2. *(new, measured)* **`handleFor`'s FIRST step cannot see a generator at
   all.** It reads the element list by symbolically executing the iterable
   (`captureRun (evalExpr m fuelK tg.E iterE)`, VCTactic.lean:2719), and
   `callIn` is a FROZEN recursion point — `py_simp` does not unfold it, so
   `evalExpr` over `upto(n)` never reduces. The probe stops at
   "the iterable did not evaluate at the loop's entry state" and prints the
   whole 271 KB module literal saying so. A generator `for` therefore has to
   be recognised SYNTACTICALLY — callee resolves in the function table with
   `isGenerator := true` — BEFORE any captured run, i.e. in the classify
   step, not inside `handleFor`. That is a different control shape from
   every arm the walker has.
3. *(new, structural)* **The walker's invariant language has no world in
   it.** `EnvShape` (VCTactic.lean:967) carries ONE `world` expression, and
   every invariant `handleFor`/`handleWhile` build is
   `∃ slots tl, env = ⟨shape.world, …⟩ ∧ invU rest slots ∧ tailFacts`
   (VCTactic.lean:2859–2886, and the same shape at 2547 for `while`): the
   world is a CONSTANT of the loop and only locals vary. A generator loop's
   invariant cannot be written there — the
   object's configuration lives in the WORLD (`uptoWorld w n k`, one
   `Heap.push` rewritten per round), so the world must become an indexed
   slot exactly as the `RVal.int` env slots are. That reaches `EnvShape`,
   `parseEnvShape`, `mkEnvExpr`, `normalizePre`, `destructInvHyp` and all
   four obligation dischargers. It is an extension of the walker's invariant
   GRAMMAR, not an arm bolted beside `handleFor`.

What DID land on the walker is blocker 2's front edge — the syntactic
recognition, which is the half of `classify` that does not need the
invariant grammar. `isGeneratorCall` (VCTactic.lean, beside
`calleeInModule`) decides "generator?" from the function table without
running anything, and the three shapes a generator reaches the walker in now
each refuse with the rule that DOES apply:

| shape | before | now |
| --- | --- | --- |
| `for x in upto(n)` | stuck run + the whole 271 KB module literal | names `PyStmtTriple.forGen` and why the walker cannot drive it |
| `for x in g` (name bound to the object) | "…need `PyStmtTriple.forLoop` by hand" — a rule that cannot take a generator | same generator refusal, via a heap-object check on the `.ref` |
| `g = upto(n)` | "no `CallsTo` fact for callee `upto` — bring a hypothesis into scope" | says a generator HAS no `CallsTo` and cannot get one, and names `EvalsIn.genCall` / `PyStmtTriple.assignNameIn` |

The third was the worst of them: it sent the reader after a lemma that
cannot be written. A loud refusal is the documentation a user meets, and a
wrong pointer in one is worse than none.

**Re-priced.** The walker arm is **1.5–3 days at MEDIUM** (world-indexed
invariants, the `EvalsIn.genCall` front half, an `IterSteps`-fact lookup on
`findCalleeFact`'s shape) — up from the memo's 1–2 at MEDIUM-HIGH, and the
increase is entirely blocker 3. It is worth doing when a THIRD generator
consumer is wanted; the rules are usable by hand today at roughly 120 lines
per function (`total_calls`, `two_phase_calls`), and both of those were
written inside one session each.

## L4 PARTIAL — the ray rules, the FIRST agreement leaf, and the memo's frame shape REFUTED (2026-08-17)

Landing **L4** of docs/generator-tier-architecture.md, and it is a partial
one by design: the memo self-rated L4 LOW-MEDIUM ("the band that could
double"), the probe re-priced it before any of it was written, and what
landed is the coherent green subset the probe validated. L5 stays
owner-gated.

**THE MEMO'S L4 IS MIS-ADDRESSED, and the measurement says so.** L4's
content line is "the `countFrom`-frame prefix spec for one ray", and the
note that stood in `Examples/python/sunfish/genmoves_theorem.lean` said a
suspended `gen_moves` inside a ray carries `block … :: countFrom j d ::
block … :: forSeq <directions[p]> :: enumSeq <board> :: []`. Neither is
true. Stepping the SHIPPED generator twice and printing every heap
generator object (a scratch `#eval`, not a guess) gives

```
[66] gen Position.gen_moves
       [block(3), forGen(a=68), block(0), forSeq(rem=3), block(0), forGen(a=67), block(0)]
[67] gen <enumerate> [enumSeq(i=82, rem=38)]  suspended
[68] gen <count>     [countFrom(cur=61, step=-10)]  suspended
```

`count(…)` and `enumerate(…)` are CALLS: each allocates its **own**
generator object (Semantics.lean, the `count`/`enumerate` builtin arms) and
`execGen`'s `.forHere` arm dispatches on the heap object, so the consuming
`for` pushes a **`forGen`** frame at it. Only a `.listV`/`.tuple`/
`.ntuple`/`.str`/`.rangeV` iterable becomes a `forSeq`. **A `countFrom`
frame never appears in `gen_moves`' own stack** — it is the ray's inner
object's entire continuation, one `stepIter` below — and the same is true
of `enumSeq` for the board scan, which means L5's board leg inherits the
correction. Two of the five frames in the recorded shape were wrong, and a
fresh `<count>` object is allocated per RAY (68, then 69, …), which the old
shape also could not express.

So L2's `genYieldsPrefix_countFrom` is not the ray rule. It is the fact the
ray rule CONSUMES, through the object bridge.

**What landed, LeanModels/Python/VCGen.lean §"L4: the RAY"** — the three
things the corrected shape needs, all of which compiled first try (the
probe wrote them in one pass, ~80 lines):

* `countObj` / `iterSteps_countFrom` — one step of a `<count>` OBJECT:
  it hands over `cur`, advances to `cur + step`, and because a `countFrom`
  frame touches nothing but itself the `.running`/`.suspended` pair
  collapses through `IterSteps.pureStep`, so a ray round moves the world by
  exactly ONE slot write. `Heap.update_of_get?` (a live slot can always be
  written) came with it.
* `genSilent_delegateBreak` / `GenEmits.blockBreak` — **generator-internal
  `break`**, which is §L3's recorded blocker for the `bound_probe` collapse
  ("reaches BELOW `GenEmits`' polymorphic prefix"). It is expressible after
  all, and `GenEmits.blockDelegate`'s own docstring said how: put the
  enclosing loop frame INSIDE `pre`. Then `genBreak (pre ++ k) = some k`
  holds uniformly in `k` — by `rfl` at every concrete prefix — and the rule
  stays frame-polymorphic. `genSilent_delegateContinue` is the sibling
  (`gen_lab.evens`' shape).
* `GenEmits.forGenRound` / `forGenBreak` / `forGenDone` — the `for x in
  <generator>` loop at `GenEmits` altitude. Not one induction like
  `GenEmits.forSeq`: an INFINITE inner generator has no remainder list to
  induct on, so the rounds are chained by the caller and `forGenBreak` is
  where a ray ends. `forGenBreak`'s body fact is over `[.block body,
  .forGen …]` — the break unwinds past the loop frame, so body and loop
  leave together, which is exactly why no new judgment was needed.

**The gate — RAY AGREEMENT AT THE STOP LEAF, over an ARBITRARY board**
(`Examples/python/sunfish/genmoves_theorem.lean`): `ray_stop_agrees`. The
shipped `Position.gen_moves`, suspended in a ray at the `count` object
holding `j`, on a board whose square `j` the reference reads as a blocker —
the generator emits exactly the moves `Ref.ray` reports (none) and leaves
the ray frame with the count advanced and `j`/`q` bound. Board free, index
free (negative-index fold included), character free, world and frame free
apart from the two lookups the statement performs. **It is the first fact
in the repo relating what the model's generator PRODUCES to the reference
enumeration** — L1's `at?_eq_indexVal` related their board reads. It is
stated through `ms.map moveVal`, so the statement does not move when the
other leaves arrive. Underneath it: the ray projected off the shipped AST
(`gmRayS`/`gmRay`/`gmRayTarget`/`rQ`/`rStop`/`rRest`, every one an `rfl`
pin), `rQ_run` and `rStop_run` (the two statements at a symbolic board),
`ray_stop_nil` (the reference's own leaf), and two `#guard` non-vacuity
pins showing both arms of the hypothesis are reachable on the opening board
(square 91 is a blocker, square 71 is not).

**The ray's genPlan census, measured** (it decides the remaining work).
The ray body is seven statements; the first two are the landed `rQ`/`rStop`
and the other five are `rRest`, in order: `rQ` Assign → delegate; `rStop`
If → delegate; then the pawn block If → **branch** (it contains the inlined
`yield from`); the unconditional Yield → yieldHere; the crawler guard If →
delegate; and the two castling Ifs → **branch**. Seven statements, and the five
`if`s that merely `break` are all DELEGATE — their break arrives as
`execStmt`'s `.brk` flow at the top of the ray body, which is why one break
rule covers them. The inlined `yield from` lowers to
`for prom in "NBRQ": yield Move(i, j, prom)` (Json.lean), i.e. a `forSeq`
frame, so `GenEmits.forSeq` already covers the promotion leaf.

**Three measurements worth the record.**

1. *Symbolic char guards DO reduce, and L1 is why.* `py_simp` takes
   `if q in " \nPNBRQK"` at a symbolic `q` all the way to
   `if c = ' ' ∨ c = '\n' ∨ c = 'P' ∨ … then _ else _` — a decidable
   disjunction over the free character. §3's F4 contingency ("a guard
   simproc: probably NOT needed") is confirmed: no simproc was written.
2. *An UNFOLD beats a REWRITE, and this cost the most time here.*
   `ntupleMethodName`, `ntupleAttr`, `indexVal` and `normIndex` are all in
   `interpUnfolds`, so `py_simp` opens them BEFORE any lemma stated at
   those heads can fire — passing `at?_eq_indexVal` or a ground
   `ntupleMethodName … = false` to `py_simp` changes nothing, and the
   residue is the raw match. Two consequences, both now house practice for
   symbolic-board work: `self.<field>` needs the module in the unfold list
   (`py_simp [sunfish, …]`, with `maxHeartbeats 1600000` /
   `maxRecDepth 16384` — proof.lean's `rotate` budgets), and the string
   subscript is finished by hand from `at?_ok_inv` after `py_simp`, not by
   `strIndex_ok` inside it.
3. *State the statement runs over an ABSTRACT env with lookup hypotheses.*
   `Env.lookup_set_ne` is a CONDITIONAL simp lemma and `py_simp` did not
   discharge its side condition inside a captured run, so a goal written
   over `Env.set env "j" v` stalls at the lookup. Written over a free `env`
   with `hself`/`hj` hypotheses — `gen_lab`'s `evals_name` idiom — it goes
   straight through, and the caller discharges the two lookups explicitly.

**Cost, measured.** Each symbolic statement over the sunfish module literal
is ~19-23 s of elaboration (`rQ_run` with `py_simp [sunfish, …]`;
`rStop_run`, which needs no module facts, is inside that). Projecting and
`rfl`-pinning the whole ray is 4 s. The theorem file builds in 22 s total.
The VCGen §L4 rules build in 4 s.

**RE-PRICED, and this is the deliverable's other half.** The memo put L4 at
3-6 days LOW-MEDIUM. The rules were hours; the leaf was hours. What remains
is **eight more `Ref.ray` leaves and the round induction**, and it does not
decompose the way the memo implied:

* *Per-leaf work is settled in SHAPE* — project the statement, run it at a
  symbolic board, splice the frame rule — and each leaf's model side is
  1-3 statements. Call it 20-30 captured runs at ~20 s: the elaboration
  alone is 7-10 minutes of build time in that file, so it wants its own
  module rather than growing `genmoves_theorem.lean`.
* *The round INDUCTION is the real remainder, and it is not priced by the
  leaves.* From the unconditional `yield` on, the ray CONTINUES, so the
  proof needs an invariant carrying `i`, `p`, `d`, the board, and the
  advancing `<count>` object across rounds, closed against
  `ray_step`/`rayBody_map_or_const`. `GenEmits.forGenRound` is the rule for
  it and is landed; nothing exercises it yet, and that is the honest gap.
* *The pawn leaf needs `pawnBreak` agreement*, which reads the board a
  SECOND time (`self.board[i + N]`) under a short-circuit — a second
  `rQ_run`-shaped fact plus the `or` ordering.

**2-4 more days at MEDIUM** for the remaining leaves plus the round
induction, in a new `Examples/python/sunfish/genmoves_ray.lean`; the
LOW-MEDIUM band is retired because the two things that could have doubled
it — a missing calculus for the ray frame, and symbolic char guards not
reducing — are both measured and both closed. What could still stretch is
the round induction's invariant, which is the one piece with no precedent
in the tier.

## L4 REMAINDER — the round induction, the segment kit, and a WHOLE ray (2026-08-17)

Continuing §"L4 PARTIAL" in a new
`Examples/python/sunfish/genmoves_ray.lean` (the separate module that entry
asked for; `genmoves_theorem.lean` gains only four un-`private`d helpers,
whose second consumer this is). The entry priced the remainder as "eight
more `Ref.ray` leaves and the round induction" and flagged the induction as
"the one piece with no precedent". That is the piece that landed, and it
cost hours rather than days; what did NOT land is blocked on one measured
tool defect, recorded below.

**THE ROUND INDUCTION IS NOT AN INDUCTION OVER THE GENERATOR** — this is
the shape finding, and L5 inherits it. `count(i + d, d)` never exhausts, so
the model side has no remainder list and no decreasing measure;
`GenEmits.forGenDone` is unreachable on a ray and the only thing that ever
ends one is a `break`. So the induction runs on the REFERENCE's fuel and
the model side rides along in continuation-passing form: `RayRound a out st
st₂` says "the loop frame emits `out` from `st`, then behaves as it does
from `st₂`", `GenEmits.forGenRound` is its introduction rule, and composing
rounds is composing transformers. `ray_rounds` folds that over `Ref.ray`'s
fuel against the two arms of `rayBody_append_or_const`.

Two consequences worth carrying:

* `rayBody_map_or_const` (the L4 characterization) was one notch too weak.
  An arbitrary `g` does not let `ms.map moveVal` split into round-output ++
  rest; the tail-consuming leaf must be known to PREPEND a fixed list.
  `rayBody_append_or_const` is the same proof at `(pre ++ ·)`.
* `ray_rounds` runs no statement at all — the model side enters entirely
  through its two hypotheses — so it is pure `Except`/`List` reasoning,
  elaborates in seconds rather than the ~20 s a captured `py_simp` costs,
  and the leaves land underneath it one at a time without it moving.

**A WHOLE RAY, not just leaves.** `ray_crawl_agrees` is the first COMPLETE
ray in the repo: a knight or a king (`p ∈ {'N','K'}`), every round, at every
fuel, over an arbitrary board, leaving a frame the enclosing scans can
carry on from. Crawlers are exactly the pieces whose ray provably never
takes a second round (`p in "PNK"` breaks it where it starts), so
`rayBody_crawler_indep` makes `ray_rounds`' continuing case vacuous and the
induction closes without the statements past the crawler guard. It is the
first use of `ray_rounds` and the first fact relating the generator's whole
output — not one leaf — to `Ref.ray`.

**The segment kit** is the reusable half: one `GenEmits` transformer per
ray statement over a FREE trailing continuation `pre`, so the same lemma
serves a round that falls through (`pre = []`) and a leaf that breaks
(`pre = [.forGen …]`, since `break` unwinds past the loop frame and body
and loop leave together). `q_falls`, `stop_falls`, `stop_breaks`,
`pawn_skips`, `yield_emits`, `crawl_breaks`, `crawl_falls`, `block_done`.
`ray_stop_agrees` had to inline both shapes; nothing here does.

**Three house-practice measurements.**

1. *`RayLocals` is a real side condition, not a technicality.* Name
   resolution consults the LOCAL env before module globals, so over an
   abstract `env` "the frame does not shadow `Move`" must be stated or
   `rYield_evals` stalls at `match Env.lookup env "Move"`. Stated once as
   "the frame binds nothing but `gen_moves`' own locals", which is true and
   stable under the ray's own writes (`j`, `q`, `prom` are in the list).
2. *A guard must be rewritten to its CONSTANT before `py_simp` runs.*
   Handed `strContains "PNK" (singleton p) = Ref.inStr p "PNK"`, the two
   crawler guards expand into a nine-character disjunction and the run
   times out; handed `= bp` with `bp` case-split first, each of the four
   arms is cheap. This generalizes `rStop_run`'s trick into a rule.
3. *One-character string equality is not `rfl` in this Lean* (a `String` is
   no longer a `List Char`). `sing_eq` goes through
   `String.toList_singleton`; `strContains_singleton` had only the
   containment half. Also: the `_lit` pins are PRINTED off the shipped AST
   with spans blanked, not transcribed — 27 span binders by hand is how a
   pin silently stops matching the program it claims to project.

**THE BLOCKER, measured — it is `py_simp`, not the calculus.** Slider
rounds must step past the two castling `if`s, which for a piece off the
corner squares is just `i == A1` short-circuiting to false. That run
REDUCES correctly (the residual is a clean `if iv = 91 then … else …`) but
emits a proof term the KERNEL rejects: `(kernel) application type mismatch`
on an `Eq.refl` for `valEq (.int iv) rhs = match .int iv, rhs with …`,
where `rhs` is still the match-bound value of the global. `valEq` is in
`interpUnfolds` (VCTactic.lean), so it opens before the operand is in whnf.

Four runs pin it, three green:

* symbolic `Int` vs a LITERAL (`i == 91`, both truth values): green;
* symbolic `Char`-as-string vs a literal (`q == "K"`): green;
* symbolic `Int` vs a module GLOBAL (`i == A1`) inside the `and` chain: kernel mismatch;
* the same comparison ALONE, no `boolOp`: kernel mismatch.

So it is neither the `boolOp` nor symbolic `valEq` — it is specifically a
comparison whose operand arrives from module-global resolution. Passing the
condition as `(iv == 91) = false`, as `(iv = 91) = False`, or as a `valEq`
rewrite does not move it, and `interpUnfolds` is not user-editable from a
proof file. The fix belongs in `py_simp` (resolve a `.name` operand to its
value BEFORE `valEq` opens, or keep `valEq` shut on a non-whnf operand) and
wants `evals_glob`-style lemmas — `evalExpr m F st (.name g s) = .ok st v`,
uniform in `F` — as the rewrite that fires first; `evalBoolChain` is
structural and clean, so hand-stepping the short-circuit is the fallback if
the tactic is not to be touched. `crawl_falls` and `block_done` are already
proved and deliberately unused: they are the two segments that close the
continuing round the moment this clears, and then slider agreement follows
with NO new calculus, because `ray_rounds` is stated against
`rayBody_append_or_const` rather than against the statements.

**The pawn leaves are independent of that blocker** and are the rest of the
remainder. `pB0`/`pB1`/`pB2` are `.delegate` breaks (projected and
plan-pinned); `pB3` is the promotion branch whose body is
`for prom in "NBRQ": yield Move(i, j, prom)` — a `forSeq` over a string
literal, already covered by `GenEmits.forSeq` — then the `break` that
`GenEmits.blockBreak` covers. `pB1` reads the board a SECOND time
(`self.board[i + N]`) under a short-circuit, so it needs an `rQ_run`-shaped
companion plus the `or` ordering; `pB2` compares against `self.ep`/`self.kp`,
which are namedtuple FIELDS rather than module globals and so are not
exposed to the blocker.

**Cost, measured.** The whole module elaborates in 22 s. `ray_rounds` and
the reference-side lemmas are seconds; each captured `py_simp` over the
module literal is the ~20 s the previous entry priced. Triad at the cut:
`lake build` clean, `docs_check` 67/67 marked blocks, `diff_test` 1288
cases / 0 failed / 115 whitelisted-unsupported.

## L4 CLOSED (calculus half) — the blocker was `valEq`'s UNFOLD, and three whole rays (2026-08-17)

Continuing §"L4 REMAINDER". That entry ended on one measured blocker with
four pin runs; this one clears it, and the fix cost **no tactic edit at
all** — the previous entry's conclusion ("the fix belongs in `py_simp`") was
wrong, and the way it was wrong is the finding.

**THE BLOCKER, and the mechanism.** `valEq` is in `interpUnfolds`, so a
captured run DELTA-unfolds it, and simp records a delta unfold as a rewrite
proved by `Eq.refl`. That is sound wherever the match can fire. But
`evalCompareChain` (Semantics.lean:5430) parks a comparison's right operand
behind a `fun st rhs => …` until its own evaluation resolves, and simp opens
`valEq (.int iv) rhs` under that binder with `rhs` a free variable. `valEq`
lives in a **mutual block** (Semantics.lean:333-377), so at a stuck match
the elaborator accepts the `Eq.refl` — its `whnf` does smart unfolding —
and the kernel cannot. Hence `(kernel) application type mismatch` on a run
whose REDUCTION was perfect: the residual of the failing pin was literally
`⊢ ¬ iv = 91`.

Three lines pin it, and they are the measurement that redirected the fix:

```
theorem minrepro (iv : Int) (rhs : RVal) : valEq (.int iv) rhs = valEq (.int iv) rhs := by
  simp only [valEq]          -- (kernel) declaration type mismatch
theorem viaEqDef (iv : Int) (rhs : RVal) : valEq (.int iv) rhs = valEq (.int iv) rhs := by
  rw [valEq.eq_def]          -- green
```

**THE FIX: `valEq.eq_def` in the `py_simp` list.** It is the SAME rewrite
carrying a real proof, and — this is the part that corrects §L4 PARTIAL's
recorded trap — **a lemma at an `interpUnfolds` head DOES fire before the
unfold, when its LHS is the head applied to variables.** `at?_eq_indexVal`
failed not because unfolds beat rewrites in general but because its LHS was
a SPECIFIC shape that no longer matched once the inner terms had been
normalised. `eq_def`'s LHS matches unconditionally, so it wins. The house
rule is therefore narrower than recorded: *to keep a definition in
`interpUnfolds` from delta-unfolding badly, hand `py_simp` its `eq_def`.*
Zero VCGen/VCTactic edits, and the ~35-minute triad that an
`interpUnfolds` change would have cost was not spent.

**THREE WHOLE RAYS, and the round induction earns its shape.**
`Examples/python/sunfish/genmoves_ray.lean` now proves ray agreement for
three of `Position.gen_moves`' four piece shapes, all over an arbitrary
board at every fuel:

* `ray_crawl_agrees` (landed in §L4 REMAINDER) — a knight or a king;
* `ray_slide_agrees` — a bishop, rook or queen off `A1`/`H1`. **The first
  ray in the repo that takes more than one round**, so the first use of
  `ray_rounds`' `hgo` and of `RayRound`'s composition; the crawler theorem
  closed with that case vacuous. `ray_rounds` did not move — which is what
  stating it against `rayBody_append_or_const` rather than against the
  statements was for, and is now demonstrated rather than claimed;
* `ray_pawn_push_agrees` — a pawn at `d = N`. The crawler theorems assume
  `p ≠ 'P'` by necessity (`pawnBreak` is where a pawn differs), so this is
  its own shape, with the pawn block entered for the first time.

**LEAF COUNT, corrected DOWNWARD.** Four of `Ref.ray`'s nine leaves are
discharged, not eight: the stop guard, the crawler guard at both of its
reasons (a non-slider, and a capture), the CONTINUING leaf, and the pawn
block's first guard. The five that remain are named individually in the
file's closing record with the shape each needs — the castling yield (the
only ray statement whose taken arm has never been run: a board read at
`j + E`, then `self.wc[0]`, then a `yield`), the pawn's two double-move
guards, its capture guard, its promotion. **The calculus half of L4 is
finished; the remainder is captured runs of precedented shapes.**

**Five measurements worth carrying.**

1. *At a FIXED direction, Python's `and` proves the expensive reads never
   happen.* `pB1_run` shows the double move's SECOND board read is not
   evaluated at `d = N`, and `pB2_run` shows `self.ep`/`self.kp` are not —
   because the direction operand short-circuits first. Not "we did not need
   them": the shipped code does not evaluate them. This is what makes a pawn
   round as cheap as a slider's, and it is the reason `d` is a fixed
   parameter rather than a symbolic one.
2. *A tuple membership reaches `heapEq`, an ordinary `==` does not.*
   `evalCompareOpH`'s `.eq` arm has a `refFree` fast path to `valEq`;
   `valContains` on a `.tuple` goes through `heapContainsScan` straight into
   `heapEq`, which is deliberately OUT of `interpUnfolds` (a frozen
   recursion point). `heapEq_int` is the one-step bridge, and `d in (N, N+N)`
   is why it exists.
3. *A `def` in a hypothesis never meets its own value.* `Ref.N` is
   semi-reducible, so a hypothesis reading `some (.int Ref.N)` does not match
   the `-10` the module global resolves to. `have hd' : … = some (.int (-10))
   := hd` — defeq, one line — is the whole fix, and it is the same trick the
   castling runs use for `iv ≠ Ref.A1`.
4. *The reference side wants a TRICHOTOMY, not a leaf enumeration.*
   `rayBody_stop_const` / `rayBody_break_const` / `rayBody_slide_map`, made
   exclusive by `rayBody_const_not_append`, replaced §L4 REMAINDER's bespoke
   `ray_crawler_leaf` simp block and shortened it by fifteen lines; every
   later leaf classifier (`ray_slider_leaf`, `ray_slider_go`,
   `ray_pawn_leaf`) is three lines on top of it.
5. *A doc comment must come AFTER `set_option … in` / `open … in`, and a
   continuation line inside `fun k => by simpa …` must be indented past the
   tactic.* Both cost a build cycle; both are silent until they are not.

**Cost, measured.** The blocker took four scratch runs to reproduce and one
(14 s) to fix. The slider half — two castling runs, two segments, the
reference trichotomy, the round, the whole-ray theorem — was green on first
or second try throughout. The pawn half was four captured runs, six
segments, two rounds and four reference facts. The module now elaborates in
**133 s** (it was 22 s), and that is entirely captured `py_simp` runs over
the `sunfish` module literal: ten of them now, at ~13-20 s each. Triad at
the cut: `lake build` clean (3666 jobs), `diff_test` 1288 cases / 0 failed /
115 whitelisted-unsupported, `docs_check` 67/67 marked blocks. The file is +949/-78 lines for 39 new
theorems (38 added, plus `breaking_round`, which is `crawler_round`
generalised and renamed); `#print axioms` on every one of them, and on the
two landed theorems the trichotomy rewrote: `propext`/`Classical.choice`/
`Quot.sound` only, no `sorryAx` and no `ofReduceBool`.

**What L5 consumes.** Three whole-ray facts in one shape —
`∃ st', RayFrame … st'.locals ∧ GenEmits sunfish ⟨w, env⟩ [.forGen
gmRayTarget a gmRay] (ms.map moveVal) st'` — so the board scan can chain
rays without knowing which piece it is holding. `RayFrame` is the interface:
the scans hand `self`/`i`/`p` in and get them back, and `RayLocals` is what
keeps the module globals visible. The correction from §L4 PARTIAL still
stands and L5 inherits it: the board scan's own frame is a `forGen` over an
`<enumerate>` OBJECT, not an `enumSeq`.

## L4 COMPLETE — the last five leaves, and seven whole rays (2026-08-17)

Continuing §"L4 CLOSED (calculus half)". That entry finished the CALCULUS and
named five leaves as remaining, each with the shape it needed. All five are
now landed, and **`Ref.ray`'s nine leaves are discharged**: every ray
`Position.gen_moves` can enter is an agreement theorem over an arbitrary
board, an arbitrary square and every fuel.

**SEVEN whole rays**, one per shape the shipped loop distinguishes:
`ray_crawl_agrees`, `ray_slide_agrees` (both landed before),
`ray_castA_agrees`/`ray_castH_agrees` (a slider ON a corner, the castling
slide included), `ray_pawn_push_agrees` (landed before),
`ray_pawn_double_agrees`, `ray_pawn_capture_agrees`, `ray_pawn_prom_agrees`.
All seven in ONE shape — `∃ st', RayFrame … st'.locals ∧ GenEmits sunfish
⟨w, env⟩ [.forGen gmRayTarget a gmRay] (ms.map moveVal) st'` — which is what
L5's board scan consumes.

**The castling YIELD is the interesting one**, and the entry above was right
that it is the only ray statement whose taken arm had never run. On a corner
the `and` chain does not short-circuit, so `castA_test_true` is the first run
in the file to read the board at a SHIFTED index (`j + E`, not the loop's own
`j`) and the first to subscript a namedtuple FIELD (`self.wc[0]` — a value
tuple, so no heap read). It also makes a round emit TWO moves, which is the
first real use of `ray_rounds`' `pre` being a LIST: `ray_slide_agrees`'
rounds always prepend a singleton, and nothing about the induction moved.

**Five measurements worth carrying.**

1. *A board read inside a `boolOp` chain does NOT go through
   `at?_eq_indexVal`.* Its LHS is `indexVal` applied to CONSTRUCTORS, and an
   `interpUnfolds` delta beats a specific-shape LHS — which is §L4 CLOSED's
   corrected rule applied, not contradicted. What `py_simp` leaves is
   Python's negative-index fold verbatim, so `board_read_facts` packages the
   four rewrites that close it (`hkeq`/`hk0`/`hklt` and the `getD`), and both
   new board reads — the castling one and the double move's second one — are
   then the same three lines `rQ_run` writes by hand. Generalize the
   RESIDUAL, not the bridge.
2. *Fork a symbolic guard before `py_simp`, and only where the chain cannot
   step.* `pB2_run_cap` must case-split `q == "."` and `j != self.ep` because
   `evalBoolChain` cannot pass an undecided operand — but its LAST operand
   needs no fork, since `abs(j - self.kp) > 1` is consumed only by the
   statement's own truthiness, and a `split` AFTER the run closes it by
   `omega`. Six captured runs where eight looked necessary. (`absInt_natAbs`
   is the one-line bridge from the model's `if x < 0 then -x else x` to the
   reference's `Int.natAbs`.)
3. *`GenEmits.forSeq`'s invariant should carry the FRAME, not the loop
   variable.* The promotion loop's `Inv` is "the world is unchanged and
   `RayFrame` holds and `j` is still bound" — no mention of `prom` at all,
   because `prom` is one of `rayNames` and every iteration re-establishes the
   frame by `RayFrame.set`. The rule's own `∃ st₂` is then exactly the
   existential the whole-ray theorem wants, so the four-element loop costs
   ONE `hstep` and no plumbing. Hand-unrolling four iterations was the
   alternative and it is longer and pins less.
4. *`cases h : e` GENERALIZES `e` in the goal.* Extracting "the second board
   read succeeded" with `cases h2 : at? b (i + N)` silently rewrote the
   goal's own mentions of that read, and the leaf classifier stopped
   typechecking with an `And.intro` type mismatch that pointed nowhere near
   the cause. The fix is the `hat` pattern the whole-ray proofs already use:
   prove `∃ c2, at? b (i + N) = .ok c2` inside a `have`, then `obtain`.
5. *A `def` in a hypothesis never meets its own value — in BOTH directions.*
   `hnear : i < A1 + N` does not close a goal that says `i < 81`, and
   `href2 : at? b (i + N) = …` does not match `at? b (i + -10)`; one defeq
   `have` at the numeral each time. §L4 CLOSED recorded this for `Ref.N` in a
   lookup; it holds for every folded constant a reference lemma mentions,
   and unfolding `N`/`A1`/`W`/`E` in the `simp` set is what exposes it.

**Cost, measured.** 77 new declarations (`#print axioms` on every one:
`propext`/`Classical.choice`/`Quot.sound` only — no `sorryAx`, no
`ofReduceBool`), +2093/-50 lines. Fifteen new captured `py_simp` runs over
the `sunfish` module literal, so the module now elaborates in **342 s** (it
was 133 s) and that is almost entirely those runs. Zero VCGen/VCTactic
edits — again. Triad at the cut: `lake build` clean (3666 jobs, no
warnings), `diff_test` 1288 cases / 0 failed / 115 whitelisted-unsupported,
`docs_check` 67/67 marked blocks. Development was done in a throwaway module
importing `genmoves_ray` so each cycle recompiled ONE file (~2 min) instead
of the 6-minute tree; the AST pretty-printer that printed the new `_lit`
pins lived there too and went with it.

**What L5 needs, and it is not the ray.** The board scan is a `forGen` over
an `<enumerate>` OBJECT (the §L4 PARTIAL correction stands), it must skip a
square whose piece is not ours (`if p not in "PNBRQK": continue` — the tier's
first `continue`, `genSilent_delegateContinue` is the rule and it is landed),
and the direction scan is `for d in directions[p]`, a subscript of a
module-global DICT, which is a heap read no ray performs. `Ref.piece` and
`Ref.refMoves` are the reference sides; `refTriples_flatten`
(genmoves_theorem.lean) is the presentation lemma they arrive through.

## L5 LANDED — the two scans, and the generator agrees with the reference (2026-08-17)

Continuing §"L4 COMPLETE". The ray was finished there; what was left of
`Position.gen_moves` was the two loops ABOVE it, and both are now proved
against the reference. **`gen_moves_yields_ref`
(Examples/python/sunfish/genmoves_scan.lean) is the first
generator-producing FUNCTION in this repo whose whole output is proved
equal to its reference enumeration**, over an arbitrary board:

```
theorem gen_moves_yields_ref (w : World) (dad : Addr)
    (b : String) (score ep kp : Int) (wc0 wc1 bc0 bc1 : Bool) (rf : Nat)
    (ms : List Ref.RefMove)
    (hg : Env.lookup w.globals "directions" = some (.ref dad))
    (hobj : Heap.get? w.heap dad = some dirsObj)
    (href : Ref.refMoves b.toList wc0 wc1 ep kp rf = .ok ms) :
    ∃ st', GenYields sunfish ⟨w, [("self", posOf b score wc0 wc1 bc0 bc1 ep kp)]⟩
      [.block gmB] (ms.map moveVal) st'
```

Board free (an arbitrary `String`), rights/ep/kp free, the reference's own
step budget free, every fuel above a threshold, and `[.block gmB]` is the
frame stack the interpreter itself builds for the method — projected off
`sunfish`, never retyped. The two world hypotheses are the module-global
`directions` dict, and `initWorld sunfish` satisfies both (`#guard`ed).

**The tier, end to end.** `piece_agrees` is square agreement (every ray of
one piece, in `directions[p]` order = `Ref.piece`); `dir_scan` is the
direction loop; `board_scan` is the enumerate loop; `ray_agrees` is the
dispatch that turns nine ray theorems into one statement over `p` and
`d ∈ directions p`.

**What the ray's interface had to gain, and it is the finding of this
landing.** L4's whole-ray theorems concluded `∃ st', RayFrame … st'.locals
∧ GenEmits …` — the world of `st'` unconstrained. **That existential loses
exactly what a scan needs**: the direction scan re-reads the `directions`
dict after every ray and the board scan holds a live `<enumerate>` object
across all of them, so a ray that says nothing about the world cannot be
composed. `SlotOnly a w w'` (globals equal, every slot but `a` equal) plus
`RayExit` (the frame AND that) is the fix, threaded through `ray_rounds`'
`Inv`/`Out` in all eight whole-ray theorems: 40 mechanical edits and
**no change to the elaboration time** (336 s, was 342 s), because the new
conjunct never meets `py_simp`. Two shape notes: `RayExit` is a DEF and
not two conjuncts because `ray_rounds` concludes `Out st' ∧ GenEmits …`, so
spelling `Out` as a conjunction associates the wrong way and every consumer
pays for it; and a name collision (`hpr` for the promotion flag) is what
the first rebuild caught, which is the argument for one bundled predicate
over one hypothesis per fact.

**`Ref.directions 'P'` crossed with the promotion test is EIGHT cases, and
L4 proved six.** The two missing ones are real chess, not corner cases: a
capture that PROMOTES (a pawn on the seventh rank taking onto the last row)
and a double push whose landing square is on the last row (only reachable
from the sixth rank, where the double-move guard refuses outright and the
promotion branch is never entered). Both land here —
`ray_pawn_cap_prom_agrees`, `ray_pawn_double_near_agrees` — out of L4's own
segments; the new model-side round is one (`pawn_cap_promotes_round`, which
is `pawn_promotes_round` with the diagonal's three guards), and the new
reference-side leaf is one (`rayBody_cap_prom_const`).

**A mislabelled pin, found by needing it.** `pins_genmoves.lean`'s board
commented "promotion captures (3 moves)" does not reach that leaf: its
enemy rooks stand on 22 and 24, which blocks the pawn's push and leaves
both its diagonals empty, so the three moves it pins are the KING's. The
reference was right; the board was not the board its comment describes.
`capPromBoard` in genmoves_scan.lean is a corrected one, checked against
CPython's own `sunfish.gen_moves` on the shipped file (11 moves, eight of
them promotions) as well as against `Ref.refMoves`. The old pin is left
alone — it pins a true fact, just not the one it names.

**Six measurements worth carrying.**

1. *A heap read through a `Heap.get?` hypothesis does not fire — same rule
   as the board's.* `dirs_evals` reads a module-global dict and
   `interpUnfolds`' delta opens `Heap.get?` into its `dite` before any
   `Heap.get?`-headed rewrite can match. What goes in is the RESIDUAL — the
   bound and the element (`hlt`, `hget`) — exactly as `board_read_facts`
   packages the board's four. The rule generalizes: package residuals, not
   bridges, for anything `interpUnfolds` opens.
2. *A `continue` round is not a `GenEmits`.* `genContinue` keeps the loop
   frame, so the round starts and ends at the SAME frame prefix and no
   `GenEmits` (which consumes its prefix) can state it.
   `genEmits_silentLoop` is the shape: a `GenSilent` from `pre ++ k` back to
   `pre ++ k`, at every `k`, carries the rest of the loop. Two silent steps
   compose into it (`genSilent_forGenCons` then
   `genSilent_delegateContinue`) and the tier's first `continue` costs four
   lines.
3. *`rw` with a lambda that PRINTS identically can still fail; `rfl` on the
   whole equation succeeds.* `refMoves_eq_refScan` could not rewrite
   `Ref.refMoves`' own per-square lambda into `refSq` (`funext`-proved
   equality, same printout, no match), but the equation
   `Ref.refMoves … = List.flatten <$> (List.range b.length).mapM (refSq …)`
   holds by `rfl` — delta plus eta at the top level, where the rewriter has
   to guess a motive.
4. *`pure` is not `.ok` for `simp`.* Every `List.mapM` inversion over
   `Except` needs `[pure, Except.pure]` in the simp set or the residual is
   `Except.ok rss = pure []`, which nothing closes.
5. *A `by` block inside a term argument ends at the first line indented
   LESS than its first tactic.* Two syntax errors in this landing were
   exactly that (`(by simpa using f x\n  (y))`), and the fix is to hoist the
   `by` into a `have` rather than to re-indent — the hoisted form is what
   the round rules read like anyway.
6. *Examples do not see Mathlib's tactics.* Mathlib is a lakefile
   dependency but nothing on this path imports it, so `push_cast`/`ring` are
   unknown tactics; `omega` covers the `Nat`→`Int` casts the board scan's
   index needs.

**Cost, measured.** genmoves_scan.lean is 1184 lines / 61 declarations / 10
`#guard`s, elaborating in **70 s** — four captured `py_simp` runs over the
module literal (the dict read at six keys, the two allocating calls, the
`continue` guard) and nothing else expensive, because the scans' own proofs
never touch the interpreter. genmoves_ray.lean +150/-72 (the interface, its
four heap lemmas, and the handoff note). Zero VCGen/VCTactic edits again —
the four rules the scans needed (`genSilent_forHereGen`,
`iterSteps_enumSeq`, `iterSteps_enumDone`, `genEmits_silentLoop`) are stated
module-polymorphically in the example file and belong beside VCGen §L4's
when something else wants them. `#print axioms` on all 76 declarations
of the new module plus the ray tier's strengthened eight and its frame kit:
`propext`/`Classical.choice`/`Quot.sound` only — no `sorryAx`, no
`ofReduceBool`, no `native_decide` anywhere on the path.

### The flagship's LAST step, and a DEFECT in the object-level statement

`GenMovesEqRef` (genmoves_theorem.lean) is `gen_moves_yields_ref` one level
out: about the heap OBJECT the call returns, drained by `stepIter`. It did
not land, and the two reasons are different in kind.

**1. The object-level drain bridge is missing, and it is the L2 remainder
VCGen already names.** `drain` peels one yield per `stepIter`, and
`stepIter` writes the resumption back into slot `a` before every step. The
frame-level chain never writes that slot, so after the body runs it still
holds the STALE `.running` object while the object-level chain holds the
current one: the two chains sit at heaps differing exactly at `a`, and
stepping them in lockstep needs "`execGen` does not depend on slot `a`" — a
LOCALITY property of the interpreter, not a fact about `gen_moves`.
Inverting the frame-level fact does not dodge it (`GenYields` is a
`drainGen` fact and `GenEmits` a transformer over one; neither exposes a
per-yield `GenSteps` at the object-level world), and an object-level
calculus mirroring `GenEmits` would need the same property to import the
ray theorems. Decomposition: land the locality lemma (a read/write-set
discipline on `execGen`, or a generator-slot-indexed frame rule), then the
bridge is an induction on the emitted list. Same mechanism unblocks
`sf_order`'s `bound_probe` (§L3's remainder), so it serves two consumers.

**2. `GenMovesEqRef` as written is FALSE.** `drain` runs every step at a
CONSTANT fuel — `stepIter sunfish 16384 w a` — while the statement
quantifies over an arbitrary board. Take `b` to be twenty thousand `'.'`
characters: the reference answers `.ok []` (no square holds one of ours) so
the hypothesis is satisfied, but a single `stepIter` has to cross every
square before the scan can report exhaustion and `execGen` charges a fuel
unit per frame step, so that step times out, `drain` answers `none`, and
the equality fails at EVERY `F`. The statement is unprovable because it is
untrue, and no amount of proof effort would have said so.

The repair is one line and it is the statement's own stated intent — its
note 4 says "`genMovesOf` runs at a single fuel `F` for both the call and
the drain", which the code does not do: `drain` would take `F` and pass it
to `stepIter`. **Not made here.** The statement is owner-decided
(§H4, commit f536d93), and a landing that cannot also prove the repaired
form is not the one that should edit it. `GenMovesEqRef` therefore stays
exactly as it was, with the defect recorded at its own file
(genmoves_scan.lean's closing section) and here.

## L6 LANDED — the WHOLE drain, and the interpreter locality property under it (2026-08-17)

Continuing §"L5 LANDED", whose closing section named the tier's last
technical gap and got the mechanism right. **The object-level drain bridge is
landed, the flagship's object level with it, and the locality property they
rest on is now a stated `Prop` with a measured price rather than a sentence
in a note.** Three things came out of one landing:

1. **`IterDrains.of_genYields`** (LeanModels/Python/VCGen.lean §L6) — *the*
   whole-drain bridge, L2's recorded remainder: a frame-level `GenYields`
   fact about a suspended object's stored continuation IS that object's whole
   `drainIter`. Induction on the emitted list, exactly as §L5 predicted.
2. **`gen_moves_drains_ref`** (Examples/python/sunfish/genmoves_drain.lean) —
   the shipped `Position.gen_moves` CALLED and its generator DRAINED yields
   exactly `Ref.refMoves`' moves in `Ref.refMoves`' order, over an arbitrary
   board, at one fuel threshold for the call and the drain both.
3. **`iterDrains_enumSeq`** — a whole drain with NO hypothesis at all, for
   every generator whose frames are heap-blind (`enumerate`'s are), which is
   the half of the bridge that needed nothing and now has a `#guard`-free
   concrete smoke in VCGen's own test section.

Both (1) and (2) carry `PayloadBlind sunfish` as an explicit HYPOTHESIS. It is
not proved here, and the rest of this entry is why that is the honest cut.

### The property, exactly

`PayloadBlind m` (VCGen.lean §L6) — *the interpreter cannot observe the
payload of a RUNNING generator object*:

```
def PayloadBlind (m : Module) : Prop :=
  ∀ (F : Nat) (a : Addr) (qname : String) (locals₀ : REnv) (cont₀ : GenCont)
    (st st₁ : FrameState) (k : GenCont) (r : Option (RVal × GenCont)),
    Heap.get? st.world.heap a = some (.generator qname locals₀ cont₀ .running) →
    execGen m F st k = .ok st₁ r →
    Heap.get? st₁.world.heap a = some (.generator qname locals₀ cont₀ .running) ∧
    ∀ (locals₁ : REnv) (cont₁ : GenCont) (h h₁ : Heap),
      Heap.update st.world.heap a (.generator qname locals₁ cont₁ .running) = some h →
      Heap.update st₁.world.heap a (.generator qname locals₁ cont₁ .running) = some h₁ →
      execGen m F ⟨{ st.world with heap := h }, st.locals⟩ k
        = .ok ⟨{ st₁.world with heap := h₁ }, st₁.locals⟩ r
```

Two conjuncts: **STABILITY** (a decided run leaves that slot exactly as it
found it) and **TRANSPORT** (replacing the payload changes nothing — same
result, same locals, same heap off `a`). The first conjunct **is** L2's
recorded "heap-stability side condition", and the shape finding of this
landing is that it is not a side condition at all: it is derivable from the
same guard the second one rests on, so nothing has to be assumed about the
body (`GenSteps.slot_stable`).

**Why it is the right generality — three narrowings that all matter.** An
arbitrary OBJECT at `a` is observable (a list is not a generator, and the
`for`-dispatch and every refusal message name the constructor); a
`.suspended` payload is observable (`stepIter` resumes it); `qname` is
observable (`repr` and the type errors print it). Widen any of the three and
the property is FALSE. Narrow it further and the bridge does not close, because
the two chains differ in exactly this way and no less: the frame chain holds
`running (locals₀, cont₀)` — the entry write of the FIRST step — while the
object chain holds `running (localsₙ, contₙ)` at step *n*.

**Why it is TRUE, censused rather than asserted.** `stepIter` is the
interpreter's ONLY reader of a generator object's `locals`/`cont`: of the
occurrences of `Obj.generator` in Semantics.lean, exactly one BINDS those
fields (`stepIter`, line 5929) and it answers `.valueError "generator already
executing"` on `.running` before reaching either. Every other occurrence
either binds nothing — the payload-blind `.generator ..` of the type name,
the `for`-dispatch, the subscript/len/attr refusals, the identity-hash
refusal, the drain refusals in `sortedValH`/`extremumValH` — or is a
catch-all that never mentions the constructor (`reprVal`'s `none`, `heapEq`'s
cross-type `false`). The same guard is why no run can WRITE the slot:
`stepIter` is also the only writer, and it refuses first.

### Why it is not PROVED here, measured

It is an 18-conjunct mutual induction on fuel over the interpreter's block —
the shape of ClockErase.lean's `clockErase`, and strictly bigger than it:

* the block is **1976 lines** with **119 heap-consuming call sites**, across
  **34 distinct heap-reading helpers**; four of those helpers are mutual
  inductions of their own (`heapEq`, `reprVal`, `keyHasInstanceRef`,
  `unhashableName?`) and three more are recursions needing their own lemma
  (`setDedup`, `dictBuild`, `unpackSeq`);
* clock erasure got to leave every heap term SYNTACTICALLY IDENTICAL on both
  sides (`withClock` moves one field nothing reads), so its per-arm work was
  congruence plumbing. A heap that differs at one slot does not: every one of
  those 119 sites needs a helper-level lemma saying the read is blind to the
  difference, and the two runs' worlds are related rather than equal, so
  every `bind` continuation is applied at two different states;
* ClockErase.lean is **2662 lines** for the easier relation, **1798** of them
  in the per-member arms (`ceEvalExpr_succ` alone is 1070).

So: a `Prop`-valued definition, `GenMovesEqRef`'s precedent — the claim
recorded, "proved" left unclaimed, and every theorem that consumes it saying
so in its signature. `#print axioms` on the whole path is
`propext`/`Classical.choice`/`Quot.sound`; there is no `sorry` and no axiom
standing in for the property.

**What was tried and rejected before settling on it.** (a) *A reachability
discipline* ("the run never reads `a` because nothing points at it") — needs a
reachability invariant preserved through allocation and every write, which is
a bigger induction than the payload one AND needs a consumer-side hypothesis
the payload version does not. (b) *A "blind" refinement of the calculus*
(`GenEmitsBlind`, every rule re-proved under a slot-`a` perturbation) — the
leaf obligations would be nearly free, because the captured runs are already
stated at a symbolic world with address-specific hypotheses, but the composed
ray/scan theorems (thousands of lines, 336 s of elaboration) would all have to
be restated. (c) *An object-level calculus mirroring `GenEmits`* — coherent,
and it hits the same wall for the same reason (§L5 said this; it is right).
(d) *Instantiating the frame-level theorem at the perturbed world* — the
theorem IS ∀-world with two hypotheses that survive a perturbation at `a ≠
dad`, and the yields match, but the per-step resumptions it hands back are
existential, so nothing forces the two chains' continuations to agree. That
last one is the trap worth recording: the ∀-world form looks like it dodges
the property and does not.

### What the three consumers have now

* **The `drainIter` bridge (L2's remainder)** — CLOSED. Unconditional for
  heap-blind frames; conditional on `PayloadBlind` in general.
* **The flagship** — `gen_moves_drains_ref`. `GenMovesEqRef` itself is
  untouched, as its own defect note requires: it drains through `drain`,
  which passes a CONSTANT 16384 to every `stepIter` while quantifying over an
  arbitrary board, and is therefore false as written (§L5). With that
  statement repaired the way its note 4 says it was meant to be — `drain`
  taking `F` — the remaining step is the value-shape move from
  `ms.map moveVal` to `refTriples ms`, which is `drain`'s own `Move`
  projection over the same list.
* **`sf_order`'s `bound_probe`** — the bridge is its engine, and three things
  beyond it are still open, now stated at the level of what they are: a
  `sorted`-over-a-GENERATOR expression rule (the builtin arm drains through
  `drainIter` and then allocates the sorted list, so `IterDrains` supplies
  the drain but not the statement), generator-internal `break` at the
  loop-frame level (§L3's remainder, unchanged), and `callClosure`'s
  generator arm for the lowered generator EXPRESSION. Not built here — it is
  `sf_order`'s own plan.

### Findings worth carrying

1. *A drain fact INVERTS, and that is what makes it walkable.* `GenYields`
   is `∃ t, ∀ F ≥ t, drainGen … = .ok`, and `GenYields.uncons` /
   `GenYields.unnil` invert it into per-step `GenSteps` facts — the missing
   primitives of L2, three lines of `Run.bind_eq_ok` each. Every object-level
   bridge over a whole drain is an induction on the emitted list through
   them, and the only thing that was ever hard is which WORLD the inverted
   facts live in.
2. *`Run.bind_eq_ok` is the inversion tool; `rw [drainGen]` beats
   `drainGen_succ` when `drainCont` is `private`.* Unfolding the driver
   directly keeps the proof text identical inside VCGen.lean and in a scratch
   file that only imports it, which is what made a 2-minute development cycle
   possible for a change whose real build is half an hour.
3. *Two writes to one slot are the second write — again, and load-bearing
   again.* The bridge's induction step needs the next round's ENTRY write
   seen at the frame-level world; `Heap.update_update` on the previous
   round's write-back is exactly that, and without it the recursion cannot
   line its two worlds up. `Heap.get?_update_self` (new, beside it) is the
   other half: a chain of object steps carries its own liveness.
4. *`set` is Mathlib's, and Examples do not see Mathlib* — §L5's measurement
   6 generalizes past `push_cast`/`ring` to the abbreviation tactics. `le_refl`
   too (`Nat.le_refl`).
5. *A theorem whose hypotheses are ALL `rfl` on a projection is the cheap way
   to meet `callIn_genCall`.* `gm_lit` bundles the found function, the four
   parameter guards, the generator flag, the call environment and the body in
   one existential closed by `⟨_, rfl, …, rfl⟩`; the alternative (naming the
   `FunctionDefn` literal) transcribes the program.

**Cost, measured.** VCGen.lean +428/-12 (§L6's twelve declarations, the two
`GenYields` inversions, `Heap.get?_update_self`, two smoke examples, and
`enumObj`/`iterSteps_enumSeq`/`iterSteps_enumDone` moved down from
genmoves_scan.lean — which is where §L5 said they would go the moment
something outside sunfish wanted them, and something now does);
genmoves_scan.lean -61 lines net. genmoves_drain.lean is 158 lines / 5
declarations. Elaboration: **VCGen.lean 1.9 s** (the whole §L6 addition
never meets `py_simp` — nothing in it touches a module literal),
genmoves_drain.lean **1.0 s**, and the price of touching VCGen.lean at all is
the tree: **29 minutes**, of which genmoves_ray is 314 s, pins_clock 913 s and
pins_bound 925 s. That ratio is the argument for developing against a scratch
file that only IMPORTS the target (2-minute cycles) and batching one real
build at the end.

**Calibration.** The gap §L5 recorded as "land the locality lemma, then the
bridge is an induction on the emitted list" was right about the second half
and wrong about the first being landable in one session: the lemma is a
ClockErase-scale build, and the useful move was to state it exactly, prove
everything that hangs off it, and price it. What that buys is a tier whose
last debt is ONE named property with a measured proof cost, instead of a
sentence in a closing note.

## L7 LANDED — the price was wrong: the perturbation is a FUNCTION (2026-08-17)

Continuing §"L6 LANDED", whose closing section stated `PayloadBlind` exactly
and priced its proof at ClockErase scale. **The price was wrong, and the
reason is one sentence: the perturbation is not a relation.** What landed is
the whole factoring plus the top-level reduction, in a new module
(LeanModels/Python/PayloadBlind.lean) that IMPORTS VCGen rather than editing
it — so the tree's expensive Examples never recompile while the proof is being
DEVELOPED (the module's own target builds in 0.9 s). The full tree is still
15m31s and is paid once per commit; that is the whole cost model.

**Third pass (same day): ALL EIGHTEEN ARMS ARE PROVED, `PBAll` is assembled
by induction on fuel, and `payloadBlind : ∀ m, PayloadBlind m` is a
theorem** — `propext`/`Classical.choice`/`Quot.sound`, no `sorry`, no side
condition, no consumer-side hypothesis. The module is 3738 lines / 135
declarations and still elaborates in 8 s (nothing in it meets `py_simp`).
The tail §"What remains, enumerated" predicted below is exactly what the
third pass paid, in the predicted order: the two named write-position pieces,
the three private equations, then `execAttrCall` (79 lines of interpreter →
105 of proof), `execStmt` (318 → 246) and `evalExpr` (1047 → 1125 — 5%
over §L6's estimate, which named ClockErase's corresponding 1070-line arm
and was the one number that pass got right).

### The shape finding

§L6 priced the proof this way: "every one of those 119 sites needs a
helper-level lemma saying the read is blind to the difference, and the two
runs' worlds are related rather than equal, so every `bind` continuation is
applied at two different states". Both halves of that are true only if the
second heap is an arbitrary heap agreeing with the first off `a`. It is not.
`Heap.update h a o` is `Array.set` under a bounds check, so its TOTAL twin

```
-- LeanModels/Python/PayloadBlind.lean (excerpt)
def Heap.swapAt (h : Heap) (a : Addr) (o : Obj) : Heap :=
  h.setIfInBounds a o
```

makes the perturbed heap a FUNCTION of the original. Three consequences,
and they are the whole landing:

1. **The relation on runs is one-directional and tiny.** `PBF`/`PBW` say a
   DECIDED base run pins the slot and forces the swapped run to be its
   image:

```
-- LeanModels/Python/PayloadBlind.lean (excerpt)
abbrev PBF (a : Addr) (o₀ o : Obj) (x y : Run FrameState α) : Prop :=
  (∀ st v, x = .ok st v → Heap.get? st.world.heap a = some o₀ ∧ y = .ok (st.swapAt a o) v) ∧
  (∀ st e, x = .exn st e → Heap.get? st.world.heap a = some o₀ ∧ y = .exn (st.swapAt a o) e)
```

   Two conjuncts, not `ClockErasedF`'s three: `.timeout` needs no arm because
   nothing in the block converts a timeout back to a decision, and
   `.unsupported` is free for the same reason `ClockErasedF` leaves it free.
   `bind`/`bindE` hand the continuation both the intermediate state AND the
   slot fact at that state — which is exactly the hypothesis an inductive
   call needs, so the "two different states" problem never arises: there is
   one state and one function of it.
2. **Every per-helper obligation is an EQUATION, not a simulation.**
   `f (Heap.swapAt h pa o) … = f h …`. That is what brings the helper tier
   into reach, and it is why the measured cost per helper is four lines.
3. **The `alloc` problem disappears.** A swap inside the heap commutes with
   `push` (`Heap.swapAt_push`) and a swap survives a write elsewhere
   (`Heap.update_swapAt_ne`, via `Heap.swapAt_comm`). Those two lemmas are
   the entire answer to "the heap moves under you", once for all 119 sites.

### What is proved

* **Tier A, the swap algebra** — `size_swapAt`, `get?_swapAt_self`,
  `get?_swapAt_ne`, `lt_size_of_get?`, `update_eq_none`, `update_eq_swapAt`,
  `update_swapAt_self`, `swapAt_push`, `swapAt_comm`, `update_swapAt_ne`,
  `get?_update_ne`, `swapAt_swapAt`, plus the `World`/`FrameState` liftings
  and their projection simp set. `Heap.get?_eq_getElem?` is what keeps each
  of these to one `simp`: it puts the tier's bounds-checked read onto
  `Array`'s mature `setIfInBounds`/`push` simp set instead of hand-rolling
  `dif` surgery.
* **Tier C, the combinators** — `ok`/`exn`/`timeout`/`unsupported`/
  `of_undecided`/`liftRes`/`bind`/`bindE`/`ite`/`push` on both `PBW` and
  `PBF`, plus `toWorld`, `withLocals`, `allocList`, `allocDict`.
  `ClockErasedF`'s geometry, arm for arm.
* **Tier B, ALL 24 of the helper equations the proved arms reach.** Two
  primitives carry them. `Heap.get?_swapAt_twin` resolves a read as "same
  object off the slot, twin generators at it". `Heap.get?_swapAt_of_ne_slot`
  is the same fact read the OTHER way — an answer that is not the slot's own
  object is at a different address — and that is exactly the shape a
  functional-induction case hypothesis (`h.get? a = some (.list xs)`) hands
  you, which is what keeps `reprVal` and `heapEq` to their `.ref` arms at 25
  and 36 lines with `simp_all` closing every other case. The five
  heap-RETURNING writers (`heapStore`, `heapAppend`, `heapPop`,
  `heapInsert`, `heapAttrStore`) are stated `map`-shaped over a new
  `Res.mapOk`, and `Heap.update_swapAt_ne` discharges each because every
  write that DECIDES is at a list, a dict or an instance — never at `pa`.
* **The 18 conjuncts, STATED** — `PBEvalExpr … PBCallClosure` in `fuelMono`'s
  order, bundled as `PBAll`, one per member of the interpreter's mutual block
  (Semantics.lean:4232-6207).
* **15 of the 18 arms** — the five composition-only members
  (`pbEvalExprs`/`pbEvalDictItems`/`pbExecStmts`/`pbDrainIter`/
  `pbAnyAllIter`) plus `evalBoolChain`, `evalCompareChain`, `execFor`,
  `execWhile`, `execForGen`, `execForList`, `callClosure`, `callIn`,
  `stepIter` and `execGen`. Each is a standalone theorem taking `PBAll fuel`
  as the IH (ClockErase's `ceEvalExpr_succ` shape), so the block's arms land
  ONE AT A TIME instead of all-or-nothing — which is what makes a partial
  landing here a green cut rather than an admitted one.
* **`stepIter`, the load-bearing arm.** §L6's census is discharged as a
  proof: at `b = pa` the slot is `.running`, so the status guard answers
  `.valueError "generator already executing"` and NEITHER payload field is
  reached — three lines. Away from `pa` the four `Heap.update` write-backs
  (Semantics.lean:5935/5944/5950/5963) go through `Heap.update_swapAt_ne`,
  and `Heap.get?_update_ne` carries the slot fact across each, which is what
  `PBF.bindE`'s continuation needs.
* **`payloadBlind_of_execGen`** — the reduction, and the point of the
  landing. §L6 said stability was derivable from the guard transport rests
  on rather than a side condition; this is that sentence as a theorem. BOTH
  of `PayloadBlind`'s conjuncts come from ONE instance of `PBExecGen`:
  stability at the IDENTITY twin, transport at the swap the consumer names,
  with `Heap.update_eq_swapAt` turning the consumer's two `update`
  hypotheses into the functional form. No glue survives the reduction — no
  side condition, no consumer-side hypothesis, nothing assumed of the body.

### The tail, as paid

**§Tier C′, the write position** — the two pieces both mutating arms
wanted, and the prediction held at 34 lines rather than 130.
`PBF.liftMapOk` threads a `map`-shaped equation into the continuation the
interpreter applies to the helper's answer; `PBF.okWrite` is the write-back
leaf (the post-write state's swap IS the swap of the post-write state — the
heap is the only field that moves, so the whole obligation is the slot fact
at the NEW heap);
`PBF.pushRef` is the same statement for an allocation. Every mutating site in
`execAttrCall`/`execStmt`/`evalExpr` is two lines over these.

**Six slot-preservation lemmas** — `heapAppend`/`heapInsert`/`heapPop`/
`heapStore`/`heapAttrStore`/`sortedValH`, each the writer's own arm
enumeration under `Heap.get?_update_ne` (or `Heap.get?_push_of_get?`, which
`sorted` and the displays need because they ALLOCATE), 14-24 lines apiece as
predicted. `Heap.ne_slot_of_twin` is the side condition all six read off:
the slot holds a GENERATOR, so an address answering a dict, a list or an
instance is a different address. `unpackStoreH`'s pin rides INSIDE its
equation as a second conjunct — one induction proves both, because both
consume the same seven-case enumeration.

**The three private equations** — `sortedValH_swapAt` (`map`-shaped through
`Heap.swapAt_push`, exactly as predicted), `unpackStoreH_swapAt` (the
`induct` principle's heap-in-the-motive shape was the whole reason this was
cheap), and `attrReadResult` — which turned out NOT to be an equation but a
`PBF` statement (`attrReadResult_pb`), because the helper is `Run`-typed:
its plan is blind (§Tier B) and every outcome carries the receiver's own
frame. One more equation the census had missed: `isClockCall_swapAt`, one
line, because `evalExpr`'s clock arm branches on the frame's LOCALS and the
world's GLOBALS and the swap moves neither.

**`PBAll` IS assembled and `payloadBlind` IS a theorem.** The fuel induction
is 27 lines, and 18 of them are the fuel-ZERO row (one `.timeout` per member,
each guarding on fuel before it looks at anything): the successor row is
`⟨pbEvalExpr_succ htwin ihn, …⟩`, one arm per conjunct, which is the whole
dividend of the arms being standalone theorems. `payloadBlind : ∀ m,
PayloadBlind m` then follows from `payloadBlind_of_execGen`, on
`propext`/`Classical.choice`/`Quot.sound`.

**The consumers are DISCHARGED, and the edge flipped to do it.** `PayloadBlind`
was DEFINED in VCGen.lean and PayloadBlind.lean imported VCGen — the right way
round while the property was being developed (a downstream module rebuilds in
seconds; §finding 3). It is the wrong way round for a discharge, because
`IterDrains.of_genYields` lives in VCGen.lean and cannot see a theorem
downstream of it. So the definition MOVED into PayloadBlind.lean, that module
now imports VC2 instead of VCGen, and VCGen.lean imports PayloadBlind: the
DAG's one edge reversed, and the five bridges (`GenSteps.slot_stable`,
`GenSteps.transport`, `GenYields.transport`, `IterDrains.of_genYields`,
`callIn_drains`) drop `(hb : PayloadBlind m)` and call `payloadBlind m`
instead. `gen_moves_drains_ref` (Examples/python/sunfish/genmoves_drain.lean)
drops it too, which is the point of the whole arc: **the sunfish drain theorem
now carries no hypothesis at all.** The flip is safe because PayloadBlind.lean
needed exactly ONE name from VCGen (the definition) and shares no `Heap.*`
name with it — checked by grep before the edit, the §L4/§L6 collision rule
applied in advance rather than fifteen minutes into the tree.


### Findings worth carrying

1. *The recursive helpers were the CHEAP ones, not the expensive ones.* §L6
   flagged four mutual inductions and three recursions among the helpers as
   aggravating factors. Lean generates a functional-induction principle for
   every one of them (`keyHasInstanceRef.induct` and friends) **whose heap is
   a fixed PARAMETER, not part of the motive** — which is exactly the motive
   shape a blindness equation needs. `unhashableName?_swapAt` is one
   `simp_all` line. `fun_induction` does NOT work on the mutual ones
   ("no functional induction theorem … or function is mutually recursive");
   `induction v using f.induct (h := h) (motive_2 := …)` does, and supplying
   `motive_2` explicitly is mandatory since nothing can infer it.
2. *`Heap` is an `abbrev`, so `h.swapAt a o` silently resolves to
   `Array.swapAt`* — which exists, takes two indices, and returns
   `Obj × Array Obj`. The failure surfaces as a type mismatch in the
   STATEMENT, which then poisons every tactic in the body with unrelated
   errors. `Heap.get?`'s own docstring records this caveat for dot notation;
   the rule is full names for every `Heap.*` operator, at every use site.
3. *A new module beats editing VCGen by two orders of magnitude.* §L6
   measured the price of touching VCGen.lean at 29 minutes because every
   Example imports the `LeanModels` umbrella transitively. A downstream
   module that IMPORTS VCGen builds in 0.9 s, so the development cycle here
   was seconds, not half an hour — and the full-tree cost is paid exactly
   once, when the module is wired into `LeanModels/Python.lean` at the cut.
   This is §L6's finding 2 (develop against a scratch file that only
   imports the target) promoted from a workaround to the module layout.
4. *Two conjuncts, not three.* `ClockErasedF` constrains `.timeout`;
   `PBF` does not need to, because the block's only `.timeout` productions
   are fuel-zero arms and faithful pass-throughs. Checking that before
   writing the relation saved an arm in every one of the combinators.

**The collision repeated, and that makes it a rule.** The second pass added
`Heap.get?_update_ne` to §Tier A and hit the SAME failure at the same two
files: genmoves_ray.lean held a local copy (different proof, identical
statement), genmoves_scan.lean opens both namespaces, and the bare name went
ambiguous — green in the module's own 0.9 s build, green in genmoves_ray's own
308 s build, and only failing at target 3665 of 3669, **fifteen minutes into
the tree**. The rule that follows: *before publishing a general `Heap.*` fact,
`grep Examples/ LeanModels/ for the name* — the local copies in
genmoves_ray.lean are where the tier's heap facts were first proved, and every
one of them is a future collision. The fix is the same both times: delete the
local copy, leave a comment in its place.

**The first collision, and why it is worth recording.** `Heap.lt_size_of_get?`
already existed as a local, byte-identical copy in genmoves_ray.lean (§L4), and
publishing the general fact made the BARE name ambiguous in genmoves_scan.lean
— which opens that namespace and the library's. The local copy is deleted and
a comment left in its place. The failure mode is worth naming: it does not
surface in the new module's own build (0.9 s, green), only in a consumer
five files downstream, 333 s into the tree. Every one of §Tier C's
combinators shares a name with `ClockErasedF`'s and `Obs`'s (`ok`, `exn`,
`bind`, `bindE`, `liftRes`, `ite`, `timeout`, `unsupported`, `withLocals`,
`toWorld`, `allocList`, `allocDict`) and NONE of those collide, because they
sit in `PBW`/`PBF` — the namespaced-combinator pattern is what makes the
tier's three transport relations coexist.

**Cost, measured.** LeanModels/Python/PayloadBlind.lean 3786 lines / 136
declarations, elaborating in **8 s** — nothing in it meets `py_simp`, and
nothing in it touches a module literal. Semantics.lean is UNTOUCHED. `#print
axioms` on every theorem in it is `propext`/`Classical.choice`/`Quot.sound`
(the writers need only `propext`/`Quot.sound`); no `sorry`, no
`native_decide`, no axiom standing in for anything. Per-arm cost across the
three passes: 18 lines median, and the three big ones landed at `execAttrCall`
105, `execStmt` 246, `evalExpr` 1125 — `evalExpr` 5% over §L6's estimate,
which named ClockErase's corresponding 1070-line arm and was the one number
that pass got right. Full-tree cost is
**15m31s**, paid once per commit and nothing to do with the proof's own
cycle.

**One tactic fact worth the line, and it cost four iterations.** `cases`
substitutes a constructor into a match WITHOUT iota-reducing it, so the
enclosing `match` stays stuck and `rw` then cannot find a pattern that sits
under the arm's pattern binders. `simp only [...]` reduces AND rewrites under
binders, so the rule is: **`simp only` for anything downstream of a `cases`
on a match scrutinee, `rw` only at the top of a goal.** Every failure in this
pass but one was that mistake, in `extremumValH`, `assignToH`, the five
writers, `stepIter` and `execGen`'s `.ref` dispatch. The dual is `simp only
[f]` at the LEAF: unfolding an interpreter member before casing its
scrutinee leaves a stuck outer match that nothing recovers — `execGen` needed
its ten frame kinds cased first and `simp only [execGen]` applied per leaf.

**Calibration.** §L6's price was a fair estimate of the wrong proof. The
useful move was not to attempt the 2000 lines it predicted but to probe
whether the obligations factor — and the factoring turned on one structural
fact about the tier's own heap API that a line count could not see. The
lesson generalizes: before paying a measured price, check whether the
measurement assumed a relation where the code offers a function.

## L8 LANDED — the three constructs `bound_probe` was blocked behind, and a FOURTH the census had missed (2026-08-17)

Continuing §"L7 LANDED". `Examples/python/sunfish/genmoves_drain.lean`'s
closing section named, verbatim, what `sf_order`'s `bound_probe` still needed
on top of the whole-drain bridge: *a `sorted`-over-a-generator EXPRESSION rule,
generator-internal `break` at the loop-frame level, and `callClosure`'s
generator arm.* **All three are landed, each with a gate theorem over the
shipped program, and a fourth construct the enumeration had missed was found by
building them.** The collapse itself is NOT reached, and §"What the collapse
still waits on" below says precisely why — it is the agreement half of the
tier, not the calculus.

Everything is in a NEW module (LeanModels/Python/GenBound.lean, 575 lines / 25
declarations, elaborating in **2.3 s**) that IMPORTS VCGen rather than editing
it — §L7 finding 3 promoted to house layout, and it held: the development cycle
was seconds throughout.

### The three, and what each actually needed

**1. `sorted` over a generator EXPRESSION** (`EvalsIn.sortedDrainRev`,
`EvalsIn.sortedDrain`). `IterDrains` (§L6) says what the argument's drain IS;
nothing said what the CALL evaluates to. Both interpreter arms (the keyword
path and the keyword-free path — a call with no keywords never reaches the
keyword dispatch, so they are genuinely two theorems) drain through
`drainIter`, order with `sortByLt` and ALLOCATE the answer, so the value is a
`.ref` at the POST-DRAIN heap's end and no pinned-state judgment can hold it.

**2. Generator-internal `break` at the LOOP-FRAME level** — and here the L4-era
note needs a correction. §L4 landed the UNWIND (`GenEmits.blockBreak`: put the
enclosing loop frame in the polymorphic prefix and `genBreak` lands at the free
continuation) and recorded it as "the piece §L3's remainder named as blocking
`bound_probe`". It is half of it. `sorted` ALLOCATES, so `execGen`'s `.forHere`
arm pushes a **`forList`** frame — and `forList` had NO `GenEmits`-altitude
rule at all, where `forSeq` has an induction and `forGen` got L4's
round/break/done trio. `GenEmits.forListRound`/`forListBreak`/`forListDone`
plus `GenEmits.forListRounds` (n whole rounds, then whatever ending the caller
has — the beta-cutoff idiom) are the loop that RECEIVES the unwind:

```
-- LeanModels/Python/GenBound.lean (excerpt)
theorem GenEmits.forListBreak {m : Module} {target : Expr} {body : List Stmt}
    {ad : Addr} {i : Nat} {xs : Array RVal} {st st₂ : FrameState} {env₁ : REnv}
    {ws : List RVal}
    (hobj : Heap.get? st.world.heap ad = some (.list xs)) (hi : i < xs.size)
    (hasg : assignToH st.world.heap st.locals target (xs.getD i .none) = .ok env₁)
    (hbody : GenEmits m { st with locals := env₁ }
      [.block body, .forList target ad (i + 1) body] ws st₂) :
    GenEmits m st [.forList target ad i body] ws st₂ :=
```

**3. `callClosure`'s generator arm** (`callClosure_genCall`,
`execStmt_nestedDef`, `EvalsIn.closureGenCall`). `callIn_genCall` is the
MODULE-function creation arm; a nested `def` that yields is a `.closure` object
whose call allocates the H4 generator with `mkCallEnv params args ++ captured`
as the stored locals. Three declarations, all of them one `rw` and one `simp`:
this was the cheapest of the three by an order of magnitude, and the
enumeration was right that it was missing.

### The FOURTH, found by building the gate rather than by reading the census

**You cannot ENTER the loop.** `genSilent_forHere` (VCGen §L2) covers a value
SEQUENCE, through `IterVals` and a pinned-state `EvalsTo`. The ordering line is
neither: it answers a `.ref` to a heap LIST, and it allocates three times
getting there. So `genSilent_forHereList` / `GenEmits.blockForList` — the
`.forHere` arm's heap-object dispatch, over `EvalsIn` — are as load-bearing as
the three that were enumerated, and no amount of reading the blocker record
would have produced them. The census names what a rule must CONCLUDE; only
composing the rules finds what they cannot be composed FROM.

A second, smaller instance of the same thing: `EvalsToList` (VC2) pins the
out-state, and the shipped ordering line's lowered genexp is called with
`pos.gen_moves()` as its first argument — which ALLOCATES. `EvalsInList` (the
effectful argument list, with `EvalsIn.genCallIn` and `EvalsIn.ntupleGenMethod`
over it) is the prerequisite that makes construct 1 usable on real code rather
than on a hypothesis.

### The gates — `Examples/python/sf_order/proof.lean`, and `sf_order` gets its
### first `proof.lean`

`spec.lean` has said "No `proof.lean` yet" since H6. There is one now, 646
lines, elaborating in **5.7 s**, with every piece of program PROJECTED out of
`sf_order` and `rfl`-pinned (`bpDef_lit`, `ordLine_lit`, `gxCall_lit`,
`gmCall_lit`, `mvBreak_lit`, `mvYield_lit`, …), so a changed program stops the
gates loudly.

* **`order_line_sorts`** / `order_line_sorts_pos` — **the shipped ordering line
  (sunfish.py 412) evaluates to the sorted list.** Everything between the
  source text and the value is discharged: `pos.gen_moves()` (a generator
  METHOD call that allocates), the effectful argument list, the genexp call,
  the `reverse=` flag's truthiness, the drain and the allocation of the answer.
  The one hypothesis left is the lowered genexp OBJECT's drain — `IterDrains`,
  §L6's own judgment.
* **`moves_loop_cuts`** — **the shipped loop with the beta cutoff.** `for val,
  move in <ordered list>: if val < val_lower: break; yield (val, move.i,
  move.j)` emits exactly the triples of the rows at or above the threshold and
  STOPS at the first row below it, with the loop frame consumed. Rows free,
  threshold free, count free, and *the tail beyond the cutting row is not
  constrained at all* — laziness is the content of the statement, and an eager
  design cannot state it.
* **`moves_def_allocates`** / `moves_call_creates` / `movesGen_eq` — the
  shipped `def moves():` allocates the closure with `depth`/`pos`/`val_lower`
  snapshotted, and `moves()` allocates the generator whose stored locals ARE
  that snapshot and whose stored continuation IS `moves`' body.

Four `#guard`s pin non-vacuity by RUNNING `bound_probe` on the opening board,
and they pin BOTH arms of the cutoff: at `depth = 0` the threshold is 40, two
of the twenty rows clear it and the probe consumes three yields (the inner
`break` fires at row three of twenty); at `depth = 1` the threshold is -100,
every row clears it and all twenty are consumed. `#print axioms` on all five
gate theorems and on all fifteen public rules is
`propext`/`Classical.choice`/`Quot.sound`.

### What the collapse still waits on, measured

Two things, neither of them one of the three:

1. **The ordering line's CONTENT** — `hdrain`. Proving `IterDrains` for the
   lowered `<genexpr@2>` is `Position.value` agreement composed with the
   `gen_moves` drain. `gen_moves_drains_ref` is exactly that theorem for the
   `sunfish` module and `sf_order`'s method body is the same text — but it is a
   different `Module` LITERAL, so the sunfish chain does not transfer without a
   module-transfer argument, and `Position.value` has no agreement theorem in
   either lane. §L3 called this "the ordering line itself, which is L4/L5";
   that is still exactly what it is.
2. **`bound_probe`'s own loop** — the `best`/`searched` fold over `moves()`
   with the OUTER cutoff. A statement-level `forGen` (`PyStmtTriple.forGen`,
   §L3) over the object gate 3 allocates, blocked on 1 rather than on any
   missing rule: the rounds it takes ARE the yields the ordering line decides.

### Findings worth carrying

1. *An enumerated blocker list is a list of CONCLUSIONS, not of premises.*
   Three constructs were named; four were needed, and the missing one
   (`genSilent_forHereList`) is the one without which the other two cannot
   meet. The way to find it was to write the gate, not to re-read the record.
2. *A module literal does NOT have to be unfolded to reason about a namedtuple
   field read.* `ntupleAttr` is in `interpUnfolds`, so `py_simp` opens it and
   no lemma stated at that head can fire (§L4 measurement 2) — but the RESIDUE
   is a `findClassAux` match on the module's class list, and one ground
   `have hfc : findClassAux sf_order.classes.toList "Move" 0 = Option.none := by
   rfl` closes it. `py_simp [sf_order, …]` on the same goal costs 15 s and then
   blows `maxRecDepth`; the pin costs **0.2 s**. That is the general recipe for
   symbolic work over an ingested module: pin the residue, never unfold the
   program.
3. *`set` is Mathlib's — again* (§L6 finding 4). It bit inside an `Examples`
   proof exactly as recorded, and the fix was to state the theorem over the
   generic value with the shipped shape as a one-line corollary, which is a
   better statement anyway.
4. *The interpreter's `sorted` has two dispatch sites, not one.* A keyword call
   and a keyword-free call take different paths through `evalExpr`, so a rule
   for one says nothing about the other. The shipped line uses `reverse=True`;
   the keyword-free arm landed beside it because the tier's other consumers
   (`sorted(<genexp>)` with no flag) are the common case elsewhere.

## L9 LANDED — `bound_probe`'s own fold, and the transport the record asked for turns out not to exist (2026-08-18)

Continuing §"L8 LANDED". That section closed with a two-item remainder: (1)
the ordering line's CONTENT, whose route was named as *transporting
`gen_moves_drains_ref` from the `sunfish` module literal to `sf_order`'s,
"`sf_order`'s method body being the same text"*, and (2) **`bound_probe`'s own
`best`/`searched` fold**, recorded as "blocked on 1 rather than on any missing
rule".

**(2) is landed, and it was not blocked on (1).** **(1) is not blocked on a
transport argument either — the premise is false, and the measurement is now a
theorem.**

### (2) The fold: `Examples/python/sf_order/bound.lean`, 4 gates, 638 lines

The fold is a theorem about what the loop does to *whatever* the generator
hands over, so the object's output is a HYPOTHESIS (`Hands` — a schedule of
`IterSteps`), exactly as `moves_loop_cuts` takes the ordered rows as one. Four
gates, each over the RAW ingested `sf_order`, every piece of program projected
and `rfl`-pinned:

* **`bound_loop_folds`** (bound.lean:282) — the shipped `for val, i, j in
  moves():` with its three-statement body, over the generator the shipped `def
  moves():` allocates. `PyStmtTriple.forGen` with a remainder-indexed
  invariant; `moves_call_creates` (§L8 gate 3b) discharges `hiter`, so the gate
  COMPOSES the L8 landing rather than restating it. Both arms in one
  statement: `probe`'s third component says whether the beta cutoff fired or
  the generator ran out, and the exhaustion hypothesis is asked for only in
  the arm that needs it — when the cutoff fires nothing at all is assumed
  about the object past the cutting yield.
* **`bound_tail_returns`** (bound.lean:334) — that loop and `return (best,
  searched)`.
* **`bound_body_returns`** (bound.lean:484) — the whole eight-statement body:
  `Position(…)`, `val_lower = QS - depth * QS_A`, the nested `def` (§L8 gate
  3a), the two accumulators, the loop, the return.
* **`bound_probe_answers`** (bound.lean:534) — **a `CallsTo` on the raw module**:
  the pair the shipped `bound_probe` returns is the beta-cutoff walk of the
  yields its own `moves()` generator hands over. The first theorem in the repo
  about a sunfish SEARCH function at the public boundary.

`#print axioms` on all five is `propext`/`Classical.choice`/`Quot.sound`.
Non-vacuity is not a hand-written list: the `#guard`s take CPython's own move
ordering (`move_order`, differentially pinned) and check that `probe` — the
spec-side walk every gate is stated against — reproduces `bound_probe`'s three
pinned runs, `(46, 1)` / `(46, 20)` / `(46, 3)`, i.e. both arms of the cutoff
and the `depth == 0` yield.

### (1) The transport: `Examples/python/sf_order/transport.lean`

The L8 record's premise — "the same text, a different `Module` literal" — is
FALSE, and pricing the two routes (parametric restatement vs re-run) was
therefore the wrong question. Measured span-blind (the `_lit` pin discipline
already quantifies spans away), `sunfish`'s `Position.gen_moves` and
`sf_order`'s agree everywhere EXCEPT the pawn-capture guard:

* shipped: `… and j != self.ep and abs(j - self.kp) > 1: break` — a
  FOUR-conjunct `and`;
* `sf_order.py`: `… and j not in (self.ep, self.kp, self.kp - 1, self.kp + 1):
  break` — THREE conjuncts, the third a `not in` over a 4-tuple.

Equivalent on integers; different ASTs. `transport.ep_guard_differs` is that,
as a theorem (conjunct census, 3 against 4, at the same position of the same
statement of the same method), and `gen_moves_bodies_differ` follows.
`Position.value` diverges the same way (`q.islower()` where the shipped file
has `q in "pnbrqk"`). Both axiom-clean.

Two things this measurement is worth beyond the refutation:

* **The promotion arm is NOT a divergence.** §L8 expected `yield from (Move(i,
  j, prom) for prom in "NBRQ")` (a lowered generator EXPRESSION) against
  `sf_order`'s hand-written `for prom in "NBRQ": yield …`. Ingestion desugars
  the first to the second: one skeleton, two instances
  (`transport.promShape`, `sf_prom_shape`, `sun_prom_shape`).
* **The fixture claims verbatim and is not.** `Examples/python/sf_order/spec.lean`
  says "`Position.gen_moves` and `Position.value` are VERBATIM from the shipped
  sunfish.py". `Examples/python/sunfish/sunfish.py` IS verbatim the shipped
  file; `sf_order.py` is not. The comment is corrected in this landing; making
  the two methods verbatim again and re-extracting is an owner call (it
  re-ingests the fixture and re-runs its pinned CPython answers) and is step 1
  of the remaining route.

### The remaining route to the collapse, in order

1. make `sf_order.py`'s two methods verbatim and re-extract;
2. THEN the transport is a real question — and the measurement says which
   route is cheap: every proof in the chain is already span-blind, so a
   module-parametric restatement is the natural form and the captured-run
   re-run is the fallback;
3. `Position.value` agreement, which no lane has;
4. `hdrain`, which discharges §5's `Hands` hypothesis and makes
   `bound_probe_answers` unconditional.

### Findings worth carrying

1. *"Blocked on X" is a claim about a STATEMENT, not about a proof.* §L8 read
   the fold as blocked on the ordering line because the collapse is. Stated
   over the yield schedule instead of over the ordered rows, the fold needs
   nothing from the ordering line — and it is the statement step 2 of the
   roadmap (depth-bounded raw `bound()`) actually consumes.
2. *A `#guard` on two ingested ASTs proves nothing: spans differ.* The first
   comparison of the two `gen_moves` bodies came back `false` and it would
   have come back `false` for a verbatim copy in a different file. The
   span-blind comparison is what carries information, and the cheap way to
   MACHINE-CHECK one is a structural census (`(andArgs …).size = 3` against
   `= 4`) rather than a span eraser.
3. *`py_simp` unfolds the guard you wanted to pin.* `hasExtraDunder`/
   `findFunction`/`dunderShaped` are all in the unfold set, so a `rfl` pin at
   that head never fires — the residue is an `∃ x ∈ m.functions, …`. Two
   recipes, both used here: restate the pin in the simp-normal form
   (`simpa [findFunction] using posF_pin`), or `split` the surviving `if` and
   kill the branch from a pinned CONCRETE projection
   (`rw [posCls_methods]; decide`). §L8 finding 2 generalizes: pin the
   residue, and the residue is whatever the unfold set leaves.
4. *A structure-instance field value may not continue on a less-indented
   line.* `{ w with heap := f\n      (arg) }` parses as `expected '}'`; the
   continuation must be indented past the FIELD NAME. Two occurrences, both
   silent until the error appeared three declarations later.

## L10 OPENS STEP 2 AT THE SHIPPED LITERAL — the raw `bound()` is projected, two gates land, and the price of the rest is measured (2026-08-18)

Continuing §"L9 LANDED". Step 2 of the model-removal roadmap is *depth-bounded
equivalences for the raw `bound()`*, and its first question was WHICH `bound()`.

### The module strategy, both routes priced

* **`sf_order` (not taken).** The machinery is there — §L9's fold, the four
  algebra lemmas, the `Hands` shape. But `bound_probe` is not `bound()`: it is
  a hand-written probe with no table, no null move, no correction and no
  recursion, and §L9's `transport.lean` already showed `sf_order.py`'s
  `Position.gen_moves`/`Position.value` are not the shipped text. Nothing
  proved there transfers to the raw goal until the owner re-aligns the
  fixture. Setup cost 0, transfer value 0.
* **`sunfish` (taken).** `Examples/python/sunfish/sunfish.py` is byte-identical
  to the engine's `sunfish.py` — re-verified this landing, `sha256
  2142d9c25435e6b55ef31fcd18142f0117f033382d1bc9eb2bfe9e3de48316ca` on both —
  and `Searcher.bound` IS the goal's function. `gen_moves_drains_ref`
  (genmoves_drain.lean) is already at this literal, so the correction arm's
  eventual dependency is in the same module. Setup cost: the whole §0
  projection layer (13 statements) stood up from scratch; per-gate interpreter
  cost 3–10x `sf_order`'s, measured below.

**Verdict: `sunfish`.** The transfer difference is categorical, the cost
difference is a constant factor.

### What the shipped `bound()` IS — thirteen statements, read not assumed

`Examples/python/sunfish/bound_depth.lean` §0 projects all thirteen and pins
each by `rfl`. Four facts the pins make precise, three of which contradict the
convenient reading:

1. **Depth 0 is NOT recursion-free.** `for val, move in sorted(…)` yields
   `-self.bound(pos.move(move), 1 - gamma, depth - 1)`, and `depth =
   max(depth, 0)` turns the `-1` child straight back into a QS node. Measured:
   `Searcher().bound(opening, 40, 0)` is **35 node entries**, `(…, 1, 0)` is 4.
   The recursion-free depth-0 cases are exactly two — the **stand-pat cut**
   (`pos.score >= gamma`, where the generator's FIRST yield `(None,
   pos.score)` cuts the fold and `pos.gen_moves()` is never reached: measured
   at **1 node**) and futility-first.
2. **At depth 0 the fold is heap-free.** The killer store inside the cutoff is
   `if move is not None and depth:` (`sbKill_lit`) — the second conjunct is
   falsy at a QS node, so no `tp_move` write happens. Measured: after
   `bound(opening, 0, 0)` `tp_move` is EMPTY and `tp_score` holds exactly one
   entry, `(pos, 0) ↦ Entry(0, 69290)`. Both are `#guard`ed.
3. **At depth 0 the correction never scans.** `if depth and not live and
   all(… for m in pos.gen_moves())` (`sbCorr_lit`) short-circuits on `depth`,
   so the `all(…)` drain — the arm that would need `gen_moves_drains_ref` — is
   dead at QS.
4. **The eviction branches carry a `Stmt.unsupported`.** `del d[k]` is out of
   tier, so `sbEvict`'s body is unsupported and every gate must show the guard
   is FALSE rather than step through it. `TABLE_SIZE = 10**6` is what buys
   that, and it is now a stated obligation rather than an accident.

Also pinned: `time.time()` sits behind the `and` in `sbClock`, so a node count
that is not a multiple of 2048 never consults the clock trace — which is what
keeps the pass-6 trace-underrun refusal unreachable below the frontier.

### The model side, read (`formal/`), and what it forces

* **The fuel model is TABLE-FREE.** `fuelValueD2 : Nat → Pos → Int`
  (`formal/Sunfish/EventuallyWide.lean`) takes no `gamma` and no table; the
  bracket it is meant to meet, `FuelBracketSpec`, quantifies a `search : Nat →
  Pos → Int → Int` with **no table parameter**, and is STATED, not proven.
  A fixed-depth refinement therefore has only two honest forms: quantify over
  all table states and land on the same `(pos, depth)` value, or restrict to a
  CLEARED table. This lane takes the second; the general stale-table case is
  step 3's, and §5 says so.
* **The model's depth 0 is a three-way LEAF** — no fold, no window, no
  recursion, `movesAbove`/`val_lower` play no part. The gamma-aware depth-0
  quiescence lives on the search side as `qsStrat`
  (`formal/Sunfish/Stalemate.lean`), whose second clause is `if gamma ≤ eval p
  then eval p`. **That clause is exactly the raw code's stand-pat cut**, and
  `fold_standpat` (bound_depth.lean:407) is it, spec-side. The depth-0
  correspondence is therefore to `qsStrat`, not to `fuelValueD2`'s leaf.
* **The model's depth 1** is the sub-horizon branch with the pass term
  collapsed to `LOSS`: each child at remaining depth 0, weight the plain
  negation, combined by `foldMax` seeded at `-MATE_UPPER` — which is the same
  seed the shipped `best, live = -MATE_UPPER, False` sets up.
* **The mate-band audit's consumable lemmas were located, not duplicated.**
  Branch `formal/band-contract`, `formal/Sunfish/BandContract.lean`:
  `tt_sentinel_defaults_never_returned` is precisely the head's
  "neither default-entry return fires under the documented window";
  `window_flip_preserves_range` is the `1 - gamma` child window;
  `windowReport_iff_boundSpec` is the vocabulary a table invariant would be
  stated in. **They cannot be imported** — `formal/` is a different Lean
  project with a different toolchain — so the two the head needs are
  re-derived locally (both are one `omega`), and the correspondence is
  recorded here rather than the lemma restated.

### What landed — `Examples/python/sunfish/bound_depth.lean`, 666 lines, axiom-clean

* **§0** — all thirteen statements of the shipped `Searcher.bound` projected
  and `_lit`-pinned (bound_depth.lean:36–271), plus the loop's target, iterable
  and three-statement body, the cutoff's body, the depth-gated killer store,
  and the probe block's four statements. Nothing retyped; a changed program
  stops every one of them.
* **§1** — the constants and the pinned residues (:276–330). `MATE_LOWER`/
  `MATE_UPPER` are *not* G1 module constants (the shipped file computes them
  from the `piece` dict, a subscript, so the fold answers `some none`); they
  come from the world's globals, and `sbF_noGlobal` is why they are invariant
  along the whole recursion.
* **§2** — the receiver and the entry frame (:333–347). `sbCallEnv` is an
  `rfl`: the four-argument call's `root` is filled from the shipped
  signature's own literal default.
* **§3** — the QS fold's vocabulary (:357–450): `Yield`/`yieldVal`/`isLive`,
  **`fold`** and `foldFrom` with the three algebra lemmas
  (`foldFrom_nil`/`_cons_next`/`_cons_cut`), **`fold_standpat`**, the
  world-threaded **`Hands`**, `LoopFrame`, `bindYield` and the `bind_eq`
  transport.
* **GATE 1 — `bound_enters`** (bound_depth.lean:476). Entering `bound` counts a
  node and does NOT read the clock: the attribute `+=` through the receiver,
  and the short-circuit that keeps `time.time()` unevaluated below the 2048
  frontier. Free world, free frame, free position.
* **GATE 2 — `max_evals`** (bound_depth.lean:502). The fold's `best =
  max(best, score)` on the shipped file, with every module-level resolution
  paid through the pinned residues instead of an unfolding of the 1MB literal.
* **§5 — `QSStandPat`** (bound_depth.lean:549), the depth-0 statement step 3
  closes, with every hypothesis one the shipped code forces.
* **§6** — six `#guard`s: the two stand-pat rows at one node each, the two
  rows that show depth 0 recursing (35 and 4 nodes), `fold` reproducing both
  stand-pat answers, and the table effect (`tp_move` empty, `tp_score` exactly
  `(pos, 0) ↦ Entry(0, MATE_UPPER)`).

`#print axioms` on `bound_enters`, `max_evals`, `fold_standpat`, `bind_eq`:
`propext`/`Classical.choice`/`Quot.sound` or less. Triad green.

### The induction template step 3 formalizes

`Hands` is world-threaded, and that is the whole induction.

At depth `d` the fold consumes a schedule `ys : List Yield`. A **searched**
entry of that schedule carries `score = -self.bound(pos.move(move), 1 - gamma,
d - 1)`, so PRODUCING it runs a child call: the child bumps `self.nodes`, may
write `tp_move`, and stores into `tp_score`. `Hands.cons`'s
`IterSteps m w a (some (yieldVal y)) w₁` says "resuming the generator at `w`
hands over `y` and lands at `w₁`" — and `w₁` is `w` plus the child's writes.

So **an induction hypothesis at depth `d-1`, of the form `callIn … = .ok w₁
(.int r)`, is consumed as one `Hands.cons` at depth `d`, with `y.score = -r`.**
Everything else is depth-independent and reused verbatim: `fold`, the three
algebra lemmas, `bind_eq`, `sbCallEnv`, and the §0 pins.

Two things change with depth and must be discharged per level, both because of
a `depth` conjunct the §0 pins now make explicit:

1. `sbKill_lit` — at `d ≥ 1` a real cutting move WRITES `tp_move[pos]`, so the
   fold is no longer heap-free and the loop invariant must carry the table;
2. `sbCorr_lit` — at `d ≥ 1` the `all(… for m in pos.gen_moves())` scan runs
   whenever `live` is false, which is where `gen_moves_drains_ref` enters this
   arc. It is already at THIS module literal, so no transport is needed.

### THE STEP-3 PROBE — the recursion rule, and what the table invariant must say

Run probe-first alongside step 2, as briefed. Three findings.

**(a) The table invariant cannot be borrowed from `formal/`.** The obvious
candidate — "every entry is `WindowReport`-valid for its key" — is stated in
`formal/`'s vocabulary over a model that HAS NO TABLE. `WindowReport gamma r s`
relates a report to a *value*; the raw table's entries are `(lower, upper)`
pairs. The invariant step 3 needs is therefore lane-local and is:

> `TableOK`: for every `((pos, depth) ↦ Entry lo up)` in `tp_score` there is a
> single value `V(pos, depth)` — the model's `fuelValueD2 … depth pos` — with
> `lo ≤ V ≤ up`, and `lo`/`up` are only ever written **post-finalizer** (after
> the correction), never mid-fold.

The "post-finalizer only" clause is not decoration: `sbStore` is statement 10,
*after* `sbCorr`, so a `tp_score` entry can never carry a pre-correction
`best`. That ordering is now a pinned fact (`sbB_split`), and it is what makes
the invariant preservable at all. The **sentinel reservation** is separate and
weaker — `-MATE_UPPER < gamma ≤ MATE_UPPER` makes the two default-entry
returns unreachable — and it is a *precondition*, not an invariant; the
mate-band audit already has it as `tt_sentinel_defaults_never_returned`.

**(b) The hard sub-case, measured: a depth-2 call probing an entry written at
depth 1.** The existing Heap machinery carries the *plumbing* and not the
*content*. Concretely: `PayloadBlind` (§L7) and the `swapAt` algebra are about
a heap perturbation at ONE slot with everything else fixed; a depth-1 child's
`tp_score` store is exactly one `dictStore` at the table's slot, so
`Heap.get?_update_self`/`_update_ne` and `Heap.swapAt_comm` do carry the
frame-separation reasoning — `bound_enters` already uses two of them and the
counter/table separation was one `rintro rfl` away. What they do NOT carry is
the *key* question: at depth 2 the probe `self.tp_score.get((pos, 2), …)`
must miss or hit-correctly against a table whose entries were keyed at depth
1, and the key is a `(Position, depth)` tuple compared by `keyEq` through a
namedtuple. That comparison is in tier (the dict-key doctrine) but there is no
lemma about it, and none of the Heap algebra is about dict CONTENTS.

**Verdict: existing machinery for the heap frame, NEW calculus for the table
contents.** The new calculus is small and specific — a `dictFind`/`dictStore`
algebra: `find` after `store` at an equal key, `find` after `store` at an
unequal key, and `keyEq` on `(Position, Int)` pairs being the conjunction of
`Position` equality and `Int` equality. Priced at **three lemmas plus a
`keyEq` congruence**, all pure (no interpreter, no module literal), i.e. the
cheapest tier of work in this repo — an hour, not a session. It is the
`probe`/`probeFrom` of step 3: the fold vocabulary for tables.

**(c) The recursion rule's shape.** `callIn`-to-self, with the IH a pair:

```
IH(d) : ∀ w pos gamma, TableOK w → WindowOK gamma →
          ∃ w' r, callIn sunfish F w "Searcher.bound" #[self, pos, gamma, d]
                    = .ok w' (.int r)
                  ∧ TableOK w' ∧ Bracket gamma r (V pos d)
```

consumed at `d+1` by turning each searched yield into one `Hands.cons` whose
`IterSteps` is the child's `callIn` (the generator's frame is suspended across
it — `PayloadBlind` is what makes that lockstep legal, and it is already
proved). `TableOK` threads through the `Hands` chain as a second conjunct of
the `forGen` invariant, beside `LoopFrame`.

### The price, measured — this is the number the next lane needs

The shipped literal is ~1MB and `initWorld sunfish` EXECUTES the module top
level. Two consequences, both measured on this box (`LEAN_NUM_THREADS=2`,
`nice 19`):

* **Kernel `rfl` on anything through `initWorld sunfish` is not affordable.**
  `theorem … : Env.lookup (initWorld sunfish).globals "MATE_LOWER" = some (.int
  47923) := rfl` exceeded 4M heartbeats and was **OOM-killed** (exit 137) after
  3m56s. The same fact as a `#guard` (compiled evaluator) is free. Recorded in
  the file at the `#guard`s.
* **One `py_simp` per STATEMENT, never per body.** The three-statement fold
  body in a single `py_simp` did not finish in **10 minutes with heartbeats
  disabled**; the same body's `max(best, score)` call ALONE, as an `EvalsTo`
  gate with the residues pinned, is **12 seconds**. The six-statement head in
  one `py_simp` exceeded 2M heartbeats at 1m47s; split into three segments,
  segment A (`[sbDoc, sbNodes, sbClock]`) lands and is the shipped
  `bound_enters`. The whole file, 666 lines with 40+ `rfl` pins, builds in
  **48–73s**.

So the remaining step-2 work is not blocked on any missing rule — it is a
known quantity at a known unit cost, and the unit is **one gate per statement,
each with its module-level residues pinned**. What is left, in order:

1. the probe block (`sbEntry`/`sbLo`/`sbUp`/`sbRep`) — the `.get` miss on a
   cleared dict and the two window returns; measured as the expensive one
   (>4M heartbeats as a single block), to be split per statement;
2. `depth = max(depth, 0)` and the mate check — one segment, needs the
   `Position`-class `score`-guard residue pinned (`c.ntBase.isSome && "score" ∈
   c.methods`, which `rfl` does not close: pin `posCls.2.methods` first and
   `decide`, §L9 finding 3's recipe);
3. the nested `def` (five captures) and `moves()` — the `sunfish` analogues of
   §L9's `moves_def_allocates`/`moves_call_creates`, mechanical;
4. the fold via `PyStmtTriple.forGen`, with `qs_round` built from
   `assignName`/`augAssign`/`ifStmt` rules over per-expression `EvalsTo` gates
   (NOT one `py_simp` — see the price above);
5. the tail (`sbCorr` off at depth 0, `sbStore`, `sbEvict`'s false guard,
   `sbRet`) and the boundary, closing `QSStandPat`;
6. then depth 1 and depth 2 by the template above, and step 3's `TableOK`.

### Findings worth carrying

1. *"Depth 0 is the recursion-free case" is FALSE for the shipped code, and the
   pins are what show it.* `max(depth, 0)` re-floors the `depth - 1` child, so
   a QS node searches QS children — 35 entries on the opening board at
   `gamma = 40`. The recursion-free depth-0 statement has to name its
   condition (`gamma ≤ pos.score`), and once named it is the model's own
   `qsStrat` clause. A depth-0 theorem written without that hypothesis would
   have been false.
2. *Two of the three `depth` conjuncts in `bound()` are load-bearing for the
   PROOF, not just the engine.* `if move is not None and depth:` and `if depth
   and not live and all(…):` are what make the QS fold heap-free and the
   correction dead — i.e. what makes depth 0 a base case at all. They read as
   optimisations in the source and are structural in the proof.
3. *The cost model of the 1MB literal is: pin the residue, gate the
   expression, never simp the block.* Isolated expression evaluation with
   pinned residues is seconds; the same expression inside a three-statement
   `py_simp` is unbounded. §L9 measured this class as "mechanical" at
   `sf_order` — it still is at `sunfish`, but only in the per-expression
   shape, and the file that ignores that does not build.
4. *A kernel `rfl` and a `#guard` are not interchangeable at this scale.* The
   `#guard` runs the compiled evaluator; the `rfl` runs the kernel on
   `initWorld sunfish`, and the kernel path OOMs. Facts about the ingested
   PROGRAM stay `rfl`; facts about the executed module-init WORLD become
   `#guard`s, and the distinction is now explicit in the file.
5. *Read the spec before choosing the statement.* `formal/`'s fuel model has no
   table and no `gamma`, so the natural-looking statement "bound refines the
   model at depth d" cannot even be typed against a stateful `callIn` without
   first deciding what the table may say. Reading `FuelBracketSpec` — which is
   itself STATED and unproven, over a table-free `search` — is what produced
   the cleared-table restriction and the step-3 `TableOK` obligation, and it
   took one read rather than a wrong theorem.

## L11 — THE TIER IS ON MASTER, and the frozen statement takes its one repair (2026-08-19)

*(Landed as §L10 in commit `d8cb1bd`; renumbered to §L11 when the step-2
lane's own §L10 merged the same day. Nothing else in it moved.)*

### The stack landed

`L2`–`L9` were eight stacked PRs, each based on the one below it. They are
merged into `master` in stack order (each retargeted to `master` after its
parent landed, so every diff shrank to its own commits before merging):

| PR | branch | merge commit |
|----|--------|--------------|
| #1 | `l2-generator-tier` | `de14906` |
| #2 | `l3-generator-tier` | `4a56967` |
| #3 | `l4-generator-tier` | `7da324c` |
| #4 | `l5-generator-tier` | `3f8c4f8` |
| #5 | `l6-drain-bridge`   | `065d763` |
| #6 | `l7-payload-blind`  | `00fda6b` |
| #7 | `l8-constructs`     | `256ce8f` |
| #8 | `l9-bound-probe`    | `7b1c2cb` |

The merges are content-free: `master`'s tree after #8 is byte-identical to
`l9-bound-probe`'s (`a018dc7`), which is what a linear stack of merge commits
should produce and is worth checking rather than assuming.

**The triad on merged master, run once and cold** (the stack was green PR by
PR; this is the first time one tree carries all of it): `lake build` 3673 jobs
green; `diff_test` 1288 cases, 0 failed, 115 whitelisted-unsupported, 1173
matched; `docs_check` 70 marked blocks, 70 ok, 15 illustrative-exempt;
`script_corpus` green. The two expensive pins re-elaborated from scratch
(`pins_clock` 1731 s, `genmoves_ray` 536 s), so a cold triad on this tree is
about an hour.

### The fuel repair, and what it closes

`GenMovesEqRef` was frozen with a defect §L5 measured and §L6 recorded: its
`drain` ran every `stepIter` at the constant fuel `16384` while the statement
quantified over an arbitrary board, so a board no single step can cross made
it false at every `F`. The owner ruled the repair — `drain` takes `F`, which
is what the statement's own note 4 always said `genMovesOf` does — and it is
made, in `genmoves_theorem.lean`, as the only change that statement has ever
taken.

Landed with it (`genmoves_drain.lean`):

* `drain_succ` / `drain_move` / `drain_done` — the drain's unfolding, stated
  by hand (see finding 1) and its two step forms;
* `drain_of_drainIter` — **the transport**: the statement's `Option`-valued
  `Move` drain IS `drainIter`, projected. Induction on the drain's fuel, with
  `stepIter_mono` absorbing the difference between the statement's single `F`
  and `drainIter`'s decreasing one;
* `gen_moves_eq_ref_of_dirs` — **the repaired flagship**, from two
  hypotheses: `initWorld sunfish` binds `directions` to `.ref 63` and slot 63
  holds `dirsObj`. Axioms `propext`/`Classical.choice`/`Quot.sound`.

### The last inch is the module INITIALIZER, and it is measured

`theorem gen_moves_eq_ref : GenMovesEqRef` is `gen_moves_eq_ref_of_dirs`
applied to two `rfl`s, and those two `rfl`s do not typecheck here. The facts
are ground and TRUE — `#eval` gives `(initWorld sunfish).heap.size = 66`,
`Env.lookup … "directions" = some (.ref 63)` and the `dirsObj` test `true`,
in well under a second — but `initWorld` RUNS the module (the `pst` pipeline:
six pieces x 120 squares through a dict-items loop, a rebound lambda, three
lowered genexps), and by kernel reduction that did not finish: at the
defaults `rfl` reports `maximum recursion depth` and then a `whnf` heartbeat
timeout; at `maxRecDepth 1000000` + `maxHeartbeats 0` the elaborator was
OOM-killed after about seven minutes on a 16 GB machine.

So the honest state of the generator tier is: `gen_moves` is proved against
the reference on an arbitrary board through the real interpreter with ZERO
hypotheses about the generator, and the flagship's remaining two hypotheses
are about module INITIALIZATION. Two routes, neither in this tier:

1. **A module-init calculus** — step `initFoldLive` symbolically, a loop
   invariant for the `pst` pipeline plus a locality argument that nothing
   after the `directions` assignment writes slot 63. This is H1's machinery
   pointed at module init, and it is the general fix: every future statement
   about the shipped program's STARTING WORLD needs it, not just this one.
2. **A pinned-literal chain** — §L8 finding 2's `project+pin` recipe, one
   top-level statement at a time, each intermediate world printed as a
   literal and re-entered by `rfl`. Bounded per step; the literals are large
   (the `pst` tables alone are 720 integers).

### Findings worth carrying

1. *An ARRAY-LITERAL pattern costs you the equational theorems.* `drain`
   matches `#[.int i, .int j, .str p]`; Lean's equation generator goes through
   `Array.getLit` under a sparse-cases motive and fails outright ("failed to
   generate equational theorem for `drain`"), which takes out `rw [drain]`,
   `simp [drain]` and `unfold drain` together. The fix is the one `Ref.ray`
   already uses next door: state the unfolding yourself and prove it `rfl`
   (`drain_succ`), then never mention the definition again. Reduction on a
   CONCRETE scrutinee is fine — only the general splitter fails.
2. *A `#guard` is a compiled check, and the gap to a proof can be a whole
   tier.* Two `#guard`s have sat next to the flagship since §L5 saying exactly
   what its last two hypotheses need. They are not proofs, and the distance
   between them and `rfl` here is not a tactic — it is 1 or 2 above. Where a
   `#guard` stands in for a fact a THEOREM needs, say so at the theorem.
3. *OPS — do not kill build processes by pattern.* `pkill -f "lake build"`
   during this pass killed two other lanes' builds on the same box along with
   this lane's (both restarted, no corruption: lake writes its trace only on
   success, so an interrupted module is simply rebuilt). Select by PID or by
   parentage. The companion rule, recorded again because it was violated
   again: never edit sources under an in-flight build — the run that was
   verifying merged master had to be discarded and restarted.


## L12 — THE MODULE INITIALIZER, PRICED: route B is REFUTED, 22 of 24 statements are proved, and the flagship's assumption becomes ONE line (2026-08-19)

§L11 closed the generator tier and left `gen_moves_eq_ref_of_dirs` with two
ground hypotheses about `initWorld sunfish`, plus two named routes for
discharging them: **(A)** a symbolic module-init calculus, **(B)** a
pinned-literal chain, one top-level statement at a time, "bounded per step".
This pass priced both against that exact goal. **The pricing changed the
plan: route B's bound is not the literal size, and it is not per statement —
there is a single Python statement the kernel cannot reduce at all.**

### What the measurements say (all on one 16 GB machine, `lake env lean`)

The shipped top level is **24 statements**; `directions` is #12 and the `pst`
pipeline is #7 (`for k, table in pst.items():`) and #8
(`K_MID, K_END = pst["K"], tuple(<genexp over range(120)>)`).

| unit | from | tool | result |
|---|---|---|---|
| statements 0–6 (imports, `version`, `piece`, raw `pst`) | scratch | `rfl` | **0.106 s** ✅ |
| statement 7, whole | scratch | `rfl` | 21.4 s to a 1 M-heartbeat timeout, 3.5 GB, **unfinished** |
| statement 7, ONE of six iterations | pinned state | `rfl` | 138 s, 6.1 GB, **OOM-killed** |
| … its body stmt 0 (`padrow = lambda …`) | pinned | `rfl` | **0.062 s** ✅ |
| … its body stmt 2 (`pst[k] = (0,)*20 + pst[k] + (0,)*20`) | pinned | `rfl` | **1.4 s** ✅ |
| … its body stmt 1 (`pst[k] = sum((padrow(table[i*8:i*8+8]) for i in range(8)), ())`) | pinned | `rfl` | 154 s to a 4 M-heartbeat timeout; **420 s / 8.5 GB to an OOM kill** at `maxHeartbeats 0` — **never finished** |
| statement 8 | pinned | `rfl` | 627 s, **OOM-killed**, unfinished |
| statements 9–23 + `resolvedG` + `Env.lookup` | pinned | `rfl` | **0.716 s** ✅ |
| the whole thing | scratch | `rfl` | OOM at ~7 min (§L11's measurement, reproduced) |

Two negative results worth as much as the positive ones:

* **Fuel is not the driver.** `initExecFuel` is 65536; the minimum fuel that
  still reproduces the shipped answer is 256 (at 128 the pipeline diverges
  and `directions` lands at `.ref 62` instead of 63 — the address is
  load-bearing). Reducing statement 7 at fuel 64 cost 25.5 s / 8.7 GB against
  21.4 s / 3.5 GB at 65536: no better, and the fuel numeral is not the cost.
* **`py_simp` is the wrong tool at this altitude.** On the wall statement it
  ran 1.02 s, expanded the 1 MB `sunfish` literal into the goal, and stalled
  at the frozen `callIn` — §L8 finding 2's rule ("pin the residue, never
  unfold the program") applies exactly. `rfl`/whnf keeps the program an
  opaque constant, which is why it gets further.

The gap that makes all of this necessary: compiled, the entire initializer is
**~0.35 s** (`#eval`), and `#guard` has confirmed these facts since §L5.

### What landed

**`LeanModels/Python/ModuleInit.lean` (316 lines, elaborates in 0.4 s) — the
module-init calculus, route A's first layer, general.** Every lemma
quantifies over `m`, `s`, `done`, `rest`; nothing mentions sunfish:

* top level — `initFoldLive_nil` / `_fold` / `_exec` / `_dirty` (+ the
  `_unsupported` and `_exn` shapes) / `_append`, and `initWorld_of_run`
  with its two projections. These are the three arms of the pipeline
  (pure fold, exec attempt, rollback-and-poison) as rewrite rules;
* one level in — `initExecStmt_items` (the dict-items shell, entered),
  `initItemsLoop_step` / `_done` (per ENTRY), `initBodyStmts_nil` / `_cons`
  (per body STATEMENT). This is the chop the residue needs.

**`Examples/python/sunfish/init_chain.lean` (1689 lines, 5.8 s) — the chain
on the shipped module.** Two pinned states (after statement 6 and after
statement 8; ~102 KB of generated literals), and then:

* `run_prefix` — statements 0–6, kernel-proved;
* `PstPipelineRuns` — **the one hypothesis**, statements 7–8, a ground
  equation between pinned literals, `#guard`ed under the compiled evaluator;
* `run_all` / `initWorld_tail` — the initializer assembled from it;
* `dirs_ref` / `dirs_obj` — **both of the flagship's hypotheses, PROVED**
  from it, each one `rfl` through the remaining fifteen statements (the
  address arithmetic that puts `directions` at slot 63, the live-view
  resolution, `resolvedG`, `opt_ranges`' rolled-back attempt, `hist`'s
  allocation and the `__main__` guard's `NameError` all run);
* `pst_loop_entered` — the items shell rule fired on the SHIPPED statement
  (no new pin): statement 7 IS `initItemsLoop` over the `pst` dict at
  address 1, six entries, from 0. The door the remaining work goes through;
* **`gen_moves_eq_ref_of_pst`** — the flagship, from that one hypothesis.

```lean
-- Examples/python/sunfish/init_chain.lean (excerpt)
theorem gen_moves_eq_ref_of_pst (hpst : PstPipelineRuns) : GenMovesEqRef :=
  gen_moves_eq_ref_of_dirs (dirs_ref hpst) (dirs_obj hpst)
```

`#print axioms` on every step and on the flagship:
`propext`/`Classical.choice`/`Quot.sound`. No `sorry`, no `native_decide`.

**Triad on the tree** (incremental over merged master): `lake build` 3676
jobs green (30.8 s); `diff_test` 1288 cases, 0 failed, 115
whitelisted-unsupported, 1173 matched; `docs_check` 70 marked blocks, 70 ok,
15 illustrative-exempt.

### So which route won

**Neither, as written — and that is the finding.** Route B got 22 of the 24
statements and then stopped, not on literal size (the biggest pin is 63 KB)
but because the chop granularity it offers is ABOVE the wall: the wall is
inside one statement. Route A's top layer turned out to be the cheap part
(11 theorems, one rewrite each, 0.4 s to elaborate) and is what carried the
22; its expensive part — a loop invariant for the `pst` pipeline, i.e.
symbolic reasoning about `sum` over a lowered genexp with a closure call per
round — is the whole of what remains. The honest split is therefore not
"A vs B" but **"A's top layer + B's pins for what fits, and A's
sub-statement layer for what does not"**, and the residue is now named to
the line rather than to the initializer.

### What the remaining work is, sized

One statement, six times (the six `pst` keys), plus statement 8's
120-round genexp. Its shape is known: `sum(<genexp>, ())` drains through
`drainIter`, so the chop is a `sum`-over-a-generator evaluation rule (the
sibling of §L8's landed `EvalsIn.sortedDrain`) plus the tier's existing
`stepIter` machinery, at ~8 rounds per iteration. Measured at ~19 s and
under 1 GB per round, that is affordable — but it is ~48 pinned mid-drain
worlds for statement 7 alone, which is an artifact nobody should generate
before trying the parametric version: the six iterations are structurally
identical (same body, different table), so ONE symbolic iteration lemma
proved over an abstract 64-tuple discharges all six. That is the next inch,
and it is route A proper.

### Findings worth carrying

1. *The array-literal pattern trap is not about `drain`.* §L11 finding 1
   recorded it at one definition; it bites `initExecStmt` too — its
   items-shell arm matches through `#[]` for the call's args and kwargs, and
   Lean fails outright with "failed to generate equality theorems for match
   expression `initExecStmt.match_3`", taking out `rw`, `simp` and `unfold`
   at that head together. The fix is the same and it is now used twice: state
   the unfolding by hand (`initExecStmt_items_unfold`), prove it `rfl`, never
   mention the definition again. **Treat this as a property of the interpreter's
   pattern style, not of one function** — any admitted shape written with a
   literal `#[]` argument list will need its own hand-stated equation.
2. *"Bounded per step" is a claim about the step, and the step is whatever
   the SOURCE says it is.* A per-statement chain inherits the source's own
   granularity, and one Python line can hold an arbitrary amount of
   computation (here: a lowered genexp, a closure call per round, and a
   fold). Before pricing a chain, price its BIGGEST step — not its average
   one, and not its literals.
3. *A `SIGKILL` is not a timeout, and the difference is the whole diagnosis.*
   Three of the runs above died at 137 (OOM kill) rather than reporting a
   Lean error; only `/usr/bin/time -l`'s peak-RSS line distinguishes "too
   slow" from "too big", and they point at different fixes. Measure both.
4. *OPS — kills by PID, never by pattern* (§L11 finding 3, respected: every
   long measurement here ran detached and was reaped by `timeout`, and the
   one orphan check was `ps` by parentage).


## L13 — STEP 3's TABLE CALCULUS LANDS IN THE GENERAL LAYER, and the step-2 re-pin turns out to be BLOCKED, not expensive (2026-08-19)

§L10 opened step 2 at the shipped `bound()` and priced step 3's remaining
obligation — a table invariant plus "three `dictFind`/`dictStore` lemmas and a
`keyEq` congruence, all pure … an hour, not a session". This pass did that, and
it also answered a question the brief put first: whether §L10's fixture still
IS the engine. **It is not, and the answer changed what the general layer had
to look like.**

### The fixture drift, measured before anything was written

`Examples/python/sunfish/sunfish.py` is the engine's file at
`sha256 2142d9c2…` — engine commit `783b0d6`, 2026-08-11 — and §L9/§L10
verified byte-identity against engine master *at that time*. Engine master is
now `e670434`; its `sunfish.py` is `sha256 f6c481a6…`.

| | pinned fixture | engine master | |
|---|---|---|---|
| commits to `sunfish.py` since the pin | — | **33** | |
| changed lines | — | **285** (187 added, 98 removed) | |
| `Searcher.bound` top-level statements | **13** | **18** | every §0 pin from index 6 on shifts |
| `Module.topLevel` statements | 24 | 27 | `LMR`, `NULL_MARGIN`, `DELAY` |
| function bodies changed | — | `__init__`, `bound`, `moves`, `search`, `main` | |
| function bodies UNCHANGED | — | `gen_moves`, `value`, `move`, `rotate`, `king_capture`, `parse`, `render` | the whole §L4–§L11 generator tier's object |

So the drift is not "#236, merged today". It is a week of engine work, and the
statement that stops is `bound_depth.lean`'s — which now carries the fact in
its own header rather than a stale claim of byte-identity.

### And the re-pin is BLOCKED — the measurement that decides the roadmap

The obvious plan ("re-extract, re-pin, pay the elaboration") was run far enough
to price it, on a scratch copy of engine master's `sunfish.py` (extractor: 0.13
s; the envelope loads and `findFunction` answers). Three `#eval`s settle it:

* `Searcher.bound`'s five `callIn` gates still pass — `(argsOk, localsOk,
  isGenerator, params.size) = (true, true, false, 5)`;
* its body carries **three** `unsupported` nodes: the two `del` statements
  (already known, guarded false by `TABLE_SIZE`) and — new — **the nested
  generator itself**:

  > `NestedDef/moves: captured name 'guard' is rebound after the def (line
  > 450) … captured name 'val' is rebound after the def (line 458) —
  > snapshot-at-def would diverge from CPython's cell`

* therefore **every** `Searcher.bound` call on current master answers
  `unsupported statement 'NestedDef'` — measured at `(gamma, depth)` =
  `(0,0)`, `(40,0)`, `(40,1)`, `(40,2)`.

The refactor moved `guard = not root and calm` BELOW `def moves():`, and H7's
nested-def tier admits only captures never rebound after the `def`. CPython is
fine — the closure reads its cell at CALL time, after the assignment — and for
`guard` the tier's refusal is CORRECT for snapshot-at-def semantics: a snapshot
taken at the `def` would read an unbound name.

The second name in the message, `val`, is worth a second look by whoever takes
the tier item: inside `moves()` it is a WALRUS target
(`(val := pos.value(killer))`), which in CPython binds `moves`'s own local, not
a cell — so the capture census appears to be over-approximating there, and the
consumer's `for val, move in moves():` is then not a rebinding of anything the
closure reads. Fixing that would remove one of the two names but NOT the
blocker: `guard` is a real rebound capture and refuses on its own.

**So re-pinning step 2 is not expensive work — it is blocked behind a tier
item: closure CELLS for captures rebound between the `def` and the call.**
That item is now the gate on all of step 2, and it is named here rather than
discovered by a lane that budgeted a re-pin.

Two things the drift does NOT touch, both measured on the new envelope:

* **The module-init tier survives verbatim.** On engine master's source
  `initWorld` still gives `heap.size = 66`, `directions ↦ .ref 63`,
  `MATE_UPPER = 69290`, `MATE_LOWER = 47923` — the three new constants are
  scalars declared after `directions`, so §L12's slot arithmetic and the
  `dirs_ref`/`dirs_obj` hypotheses are unaffected.
* **The TABLE's shape is byte-identical in both versions** — the probe
  (`entry = self.tp_score.get((pos, depth), Entry(-MATE_UPPER, MATE_UPPER))`),
  the store (`self.tp_score[pos, depth] = Entry(best, entry.upper) if best >=
  gamma else Entry(entry.lower, best)`) and `Entry = namedtuple("Entry",
  "lower upper")`. That is why step 3's work belongs in the general layer, and
  why it landed there.

### What landed — `LeanModels/Python/DictCalc.lean` (728 lines, 40 theorems, elaborates in 2.1 s)

§L10 (b)'s verdict was *"existing machinery for the heap FRAME, NEW calculus
for the table CONTENTS."* The frame half was already there (`PayloadBlind`'s
`swapAt` algebra, `Heap.get?_update_ne`). This is the other half, and nothing
in it mentions a program, a module literal or an interpreter run.

* **§1 — `keyEq` is an equivalence on the hashable keys.** Proved through a
  normal form (`keyNF` : the value a key COMPARES AS) rather than 81
  constructor pairs, with `hashableKey k = true ↔ (keyNF k).isSome` as its
  companion. `keyEq_refl` / `_symm` / `_trans` are then one line each.
* **§2 — the three lemmas §L10 priced.** `dictFind_store_self` (find after a
  store at an equal key), `dictFind_store_ne` (at an unequal key — the arm that
  actually consumes transitivity, because `dictStore` keeps the OLD stored key
  at a replaced entry), and `dictFind_sound` (whatever a probe reads really is
  stored, under a key it cannot tell apart from its own). Plus `dictStore_mem`,
  the membership shape a preservation proof reads off.
* **§3 — `Bracket` / `TableOK`.** A schema is a pair of partial functions —
  what the KEY names, what an ENTRY carries — so the module commits to no entry
  shape. `TableOK.store` (preservation) and `TableOK.find` (consumption) are
  its two rules, and both run through `KeyDetermined`, the requirement that
  keys a dict cannot tell apart name one value.
* **§4 — the same at a heap slot.** `TableAt`, preserved by `heapStore` at the
  slot and by `Heap.update` anywhere else, and read through `heapGet` — the
  `.get(k, default)` shape, whose answer is *the default, or a bracketing
  entry*. That is the shipped probe statement, minus the program.
* **§5–§7 — the HARD SUB-CASE of §L10 (b), closed.** A depth-`d` store is
  invisible to a depth-`e` probe whenever `d ≠ e`: `keyEq_pair_depth_ne` at the
  key, `dictFind_store_depth_ne` at the dict, `heapGet_heapStore_depth_ne` at
  the heap. It needs nothing about the positions, the entries or the rest of
  the table — the key comparison alone decides it, which is *less* than §L10
  expected to need.
* **§8 — the recursion rule's table half.** `Bracket.SubtreeWrites` is a child
  subtree as the parent's table sees it: any number of bracketing stores at
  other depths, plus arbitrary writes at other slots. Across it the parent's
  probe is STABLE (`probe_stable`) and the invariant SURVIVES (`tableAt`).
  These two are the "IH at depth `d-1` consumed as one `Hands.cons` at depth
  `d`" template's table obligations, discharged once and depth-generically.
* **§9 — nine `#guard`s** (depth-2 misses a depth-1 table; the depth-1 probe
  still hits; the namedtuple spelling of a key addresses the same slot;
  `True` is `1` as a depth; the entry decoder).

`#print axioms` on all fourteen headline theorems: `propext` and `Quot.sound`
— not even `Classical.choice`. No `sorry`, no `native_decide`.

**Triad, cold on the merged tree** (adding a module to the `LeanModels.Python`
umbrella re-elaborates everything downstream, so this is a full pass, not an
incremental one): `lake build` **3677 jobs green**, `DictCalc` itself 2.1 s and
the two expensive pins re-elaborated from scratch (`pins_clock` 917 s,
`genmoves_ray` 321 s — both well under §L11's 1731 s / 536 s); `docs_check` 71
marked blocks, 71 ok, 15 illustrative-exempt; `diff_test` 1288 cases, 0 failed,
115 whitelisted-unsupported, 1173 matched.

### Findings worth carrying

1. *A drifted fixture is not automatically a re-pin job — MEASURE which kind of
   stale it is.* Three `#eval`s on a scratch envelope (about ten minutes)
   separated "expensive" from "blocked", and the answer inverted the plan: the
   shipped `bound()` no longer INGESTS, so no amount of elaboration budget
   buys the re-pin. The same three `#eval`s also showed the generator tier's
   object unchanged and the module-init tier unaffected, so the drift's blast
   radius is one file, not the sunfish directory.
2. *"Written post-finalizer only" needed no clause of its own.* §L10 stated
   `TableOK` with a second requirement — entries written after the correction,
   never mid-fold. In the calculus it is not a conjunct: it is
   `TableOK.store`'s own hypothesis `S.Holds k v`, which a mid-fold `best`
   cannot discharge. The program's statement ORDER is what makes the hypothesis
   dischargeable; the invariant only has to demand it. An invariant clause that
   is really a proof obligation should be a HYPOTHESIS, not a conjunct — it
   moves the burden to the one site that can pay it.
3. *A table schema keyed on the plain-tuple spelling is UNSOUND, and the proof
   is what says so.* `keyEq` erases the namedtuple class and coerces `True` to
   `1`, so `(pos, d)`, `Key(pos, d)` and `(pos, True)` can address one slot.
   `KeyDetermined` is false for a schema that reads only `.tuple` + `.int` —
   `tpBracket_keyDetermined` does not typecheck without `pairKey`/`keyInt`
   reading both spellings. The dict-key doctrine's coercions are not a
   curiosity; they are a soundness side condition on every memo-table spec.
4. *The general layer is the drift hedge, and this pass is the evidence.* Every
   theorem above was stated against `dictFind`/`dictStore`/`heapGet`/
   `heapStore` rather than against `sunfish`, and all of it survives the very
   refactor that stopped step 2's file. When a lane's fixture is a moving
   target, altitude is not elegance — it is the only work that keeps.
5. *OPS — the array-literal trap was AVOIDED by construction, not repaired.*
   `entryBounds` decodes `Entry(lo, up)` through `xs.toList` and a `List`
   pattern instead of a `#[…]` pattern (§L11 finding 1, §L12 finding 1: an
   array-literal pattern costs the equational theorems outright). The recorded
   trap cost nothing this pass because it was read first.

### What step 3 still owes

The calculus is general and proved; what it has no consumer for is the SHIPPED
statement, and that is now gated on the tier item in §the re-pin above. In
order:

1. **closure cells for rebound captures** (H7 extension) — until it lands, no
   statement about the current engine's `bound()` can be typed at all;
2. then step 2's remaining gates on a re-pinned `bound_depth.lean` (the §0 pins
   re-projected at 18 statements, and §3's fold vocabulary restated: the fold
   target is `(val, move)`, the score is computed in the CONSUMER across five
   branches, and there is an explicit `break` on a settled cap);
3. then `tpBracket` instantiated at the engine's own `Entry`, `TableOK`
   threaded through the fold beside `LoopFrame`, and the depth-`d`/depth-`(d-1)`
   composition — for which §8's two theorems are the table half, already paid.


## L14 — CLOSURE CELLS LAND, and the named blocker turns out to be THREE (2026-08-19)

§L13 named the tier item that gates all of step 2: *"closure cells for
rebound captures (H7 extension) — until it lands, no statement about the
current engine's `bound()` can be typed at all."* It has landed, and the
engine's `bound()` now runs through the interpreter. Two things the
naming did not know, both found by measurement rather than by reading:

1. **One of the two refused names was never a capture.** §L13 flagged
   `val` for a second look; CPython's own compiler settles it. The cell
   set for `moves()` is `{guard}`, not `{guard, val}`.
2. **The cell was not the only blocker.** With it fixed, `bound()`'s
   statement census came back clean — and the RUN still refused, twice.
   The walrus in general expression position and `yield from` a
   non-genexp delegate were both in the way, and only the second was
   invisible to a node count.

### What the shipped `bound()` actually needed, in the order it surfaced

| # | blocker | how it was found | cost |
|---|---------|------------------|------|
| 1 | captures rebound after the `def` (`guard`) | §L13's census | the tier item |
| 2 | `val` reported as a capture it is not | the same census, doubted | one extractor clause |
| 3 | four `NamedExpr` nodes (`val`, `v`, `cap`, `proof`) | the census, once (1) stopped hiding the body | one `Expr` constructor |
| 4 | `yield from sorted(…)` | **the SMOKE** — the census called it supported | one ingestion arm |

Finding 3 is the one to carry: a statement-level `Unsupported` count is
not an ingestion verdict. `yield from` a non-genexp is a STRUCTURED node
that refuses at EVALUATION, so it counted as clean and would have been
reported as clean. Run the thing.

### The cell, as built

A cell is a heap slot — `Obj.cell (value : Option RVal)`, `none` for
CPython's empty cell — addressed from the frame's env under a directory
key `"<cell>x"` that no Python identifier can spell. The frame's
ordinary binding of `x` is untouched, so every existing read, write and
frame lemma survives verbatim; `allocCells` creates or REUSES the slots
when the `def` runs (one frame, one cell — which is what makes a `def`
in a loop correct); `capturesSnapshot` copies the DIRECTORY entry
instead of a value; `cellsFor` reads the cells at the CALL from the
defining frame's live locals. Details and the boundary in
docs/memory-model.md §closure CELLS for rebound captures.

**The one concession, recorded rather than hidden.** The slot's CONTENT
is never read back: under the escape admission the defining frame is the
authority, so writing the live value into the slot at each call is an
observationally invisible copy. The slot buys the cell's IDENTITY (one
per frame, shared by every closure it creates), not its storage. Two
consequences are priced: relaxing the ESCAPE admission needs the write
plus a `Res.mapOk` blindness lemma beside `heapAttrStore_swapAt`;
relaxing the GENERATOR admission (no rebinding at or after the first
call) needs a refresh at the four frame-level resume sites. Neither is
needed by anything shipped today, and both were measured before being
skipped — see "the design that was NOT taken".

### The design that was NOT taken, and why — the number that decided it

The first implementation put the cell read in `evalExpr`'s NAME arm: no
plain binding, so resolve THROUGH the slot, at every read, including a
generator's resume. That is the fully general mechanism, and it is the
one to come back to. It was abandoned on a measurement:

| | name-arm deref | read at the call |
|---|---|---|
| `Obj.cell` arms in `Semantics` | 31 | 31 |
| `Obs`/`ClockErase`/`PayloadBlind` proof arms | ~35 | ~35 |
| NEW blindness lemmas needed | `cellsFor`, `allocCells`, **+ a write-commuting `Res.mapOk` lemma**, + the name arm in `worldInv`, `pbEvalExpr`, `ceEvalExpr` | `cellsFor_swapAt`, `allocCells_swapAt`, `allocCells_get?`, `allocCells_withClock`, `allocCells_clock` |
| observable difference on the ADMITTED fragment | none | none |

The name-arm version puts a heap read on the hottest path in the three
proof files, and `PayloadBlind` is 3786 lines of delicate `swapAt`
algebra. The call-time version is observationally identical wherever the
tier admits a cell at all — the callee never WRITES one (`nonlocal` is
refused) and no admitted generator can see a later value — so the
general mechanism is in place and the general PROOF is not paid for
until an admission is relaxed.

### The capture census now agrees with CPython's compiler

`_assigned_names` did not count the WALRUS as a binding, so `moves()`'s
`val` — a walrus target, `moves`' own local — was reported as a capture
of `bound()`. Adding the clause (and subtracting comprehension targets
back out, since `_walk_scope` descends into comprehensions on purpose,
because PEP 572 leaks out of them) makes the extractor's capture set
equal `co_freevars` on **all 30 nested defs in `Examples/python` plus
the engine's `sunfish.py`** — checked against `compile()`, not asserted.
`moves()` captures `depth`/`gamma`/`guard`/`killer`/`pos`, exactly
CPython's, and only `guard` cells.

`_binding_linenos` took the same clause, which is the SOUNDNESS
direction: a walrus after the `def` is a rebinding, and without it a
capture the tier called snapshot-safe could have been rebound behind its
back.

### THE MEASUREMENT — engine master's `bound()`, end to end

On a scratch copy of engine master (`e670434`) `sunfish.py`, extracted
and driven by a five-line `probe(gamma, depth)` that builds the opening
`Position` and a fresh `Searcher`:

* `Searcher.bound` is **18 statements**, the five `callIn` gates
  `(argsOk, localsOk, isGenerator, params.size) = (true, true, false, 5)`,
  and **two** `unsupported` nodes — the two `del`s already known and
  guarded false by `TABLE_SIZE`. The `NestedDef` refusal is gone.
* Through the interpreter, against CPython on the same driver:

  | `(gamma, depth)` | CPython | model | |
  |---|---|---|---|
  | `(0, 0)` | 0 | 0 | `#guard` |
  | `(40, 0)` | 4 | 4 | `#guard` |
  | `(-40, 0)` | 0 | 0 | `#guard` |
  | `(0, 1)` | 0 | 0 | `#guard` |
  | `(40, 1)` | 37 | 37 | `#guard` |
  | `(40, 2)` | 36 | 36 | `#eval`, 75 s at fuel 400000 |

  The first five are one 43 s `lake env lean` at fuel 40000.

That is the milestone: the CURRENT engine's `bound()` ingests and RUNS.
It is a measurement, not a committed gate — pinning it would mean
re-pinning `Examples/python/sunfish/sunfish.py`, which is the frozen
§L4–§L13 stack's object. What IS committed is drift-proof:
`closure_lab.gen_cell_before_call` is `moves()`' shape (a generator
closure whose celled name is written after the def and before the first
call) and `walrus_lab.w_genexp_filter` is the shipped ordering line's.

### The re-pin, priced honestly

Nothing blocks it any more; what it costs is `bound_depth.lean`. The §0
pins were projected at 13 statements and the shipped body is 18, so
every pin from index 6 on moves, and §3's fold vocabulary is a different
program: the fold target is `(val, move)`, the score is computed in the
CONSUMER across five branches, and there is an explicit `break` on a
settled cap. The generator tier's object is unchanged (§L13 measured
`gen_moves`/`value`/`move`/`rotate`/`king_capture`/`parse`/`render`
byte-identical) and module init is unaffected, so the blast radius is
`bound_depth.lean` plus the `sunfish.json`/`sunfish.py` pin — one file
of theorems, not the directory. Budget it as its own lane; this one
spent its remainder on making the run possible.

### What landed

* `LeanModels/Python/Runtime.lean` — `Obj.cell`, its WF arm, the
  boundary-freeze refusal, two proof arms.
* `LeanModels/Python/Ast.lean` — `Expr.namedExpr`.
* `LeanModels/Python/Semantics.lean` — `cellKey`/`isCellKey`/`cellName`,
  `allocCells`, `cellsFor`, the two `*_cellFree` convenience lemmas, the
  walrus arm, the cell allocation in `defStmt`, the cell read at the
  three closure-call sites, and 32 loud `.cell` arms.
* `LeanModels/Python/Json.lean` — the `NamedExpr` parse arm, the general
  `yield from` lowering through `<yieldfrom@n>`.
* `LeanModels/Python/PayloadBlind.lean` — `allocCells_swapAt`,
  `allocCells_get?`, `cellsFor_swapAt`, and the `keyHasInstanceRef.induct`
  renumbering the new `Obj` constructor forced.
* `LeanModels/Python/ClockErase.lean` — `allocCells_withClock`,
  `allocCells_clock`, and the arm updates.
* `extractors/python/extract.py` — the walrus clauses, comprehension
  targets, the cell split, `_name_escapes`, `_first_use_lineno`, the
  general `NamedExpr` node with its comprehension-scope guard, and the
  leftmost-walrus hoist in the pass-7 filter lowering.
* `Examples/python/closure_lab` — six new cell rows; `Examples/python/
  walrus_lab` — a new lab, 7 functions.

**Triad, cold on the merged tree** (a new `Obj` constructor re-elaborates
everything downstream, so this is a full pass): `lake build` **3678 jobs
green**, zero `sorry`/`admit`/`native_decide` and zero `sorryAx` — the axiom
profile is 299 `[propext, Classical.choice, Quot.sound]`, 14
`[propext, Quot.sound]` (DictCalc's choice-free theorems, preserved) and 4
`[propext]`. `diff_test` **1315 cases, 0 failed, 113 whitelisted-unsupported,
1202 matched** — against §L13's 1288 / 115 / 1173, so the 1173 all still
match and the tier ADDED 29 while turning two whitelisted refusals into
agreements. `docs_check` 71 marked blocks, 71 ok, 15 illustrative-exempt;
`extractors/python/test_extract.py` 77 ok.

### Findings worth carrying

1. *A statement-level `Unsupported` count is not an ingestion verdict.*
   `yield from sorted(…)` is a STRUCTURED node that refuses at
   EVALUATION; the census called `bound()` clean while the run refused.
   The three `#eval`s §L13 recommended are the right first move, but the
   verdict is a CALL, not a count. This cost nothing here only because
   the smoke was run before the write-up.
2. *When a hand-rolled static analysis has an oracle, RUN the oracle.*
   The capture census had been over-approximating since H7; twenty lines
   of `compile()`-and-compare over the whole corpus found it, confirmed
   the fix, and turned "probably right" into 30 checked nested defs. The
   analysis and CPython disagreeing is a bug in exactly one of them.
3. *Put the general MECHANISM in and the general PROOF off.* The heap
   cell, the directory key and the def-time allocation are the real
   thing; only the call-time READ is the restricted step, and it is
   restricted by an ADMISSION the extractor enforces loudly. That kept
   `PayloadBlind` to three new lemmas instead of a rewrite, and every
   relaxation is now a named, priced edit rather than a redesign.
4. *A new `Obj` constructor costs the `.induct` numbering, and the
   invoice arrives in the proof files.* `keyHasInstanceRef.induct`'s
   twelve cases all shifted; the tempting fix (let the cell fall into the
   existing catch-all) would have made a cell silently HASHABLE. The
   renumber is eight lines and keeps the refusal loud — take it.
5. *OPS — the pinned interpreter is part of the fixture.* Regenerating
   the envelopes with the default `python3` (3.14) rewrote every f-string
   span and the recorded CPython version across sixty files. `python3.9`
   is what the envelopes were pinned with; the whole extraction, the
   extractor tests and `diff_test` run under it. The version field still
   moves `3.9.19 → 3.9.25` — honest provenance, one line per envelope.
6. *OPS — kills by PID and parentage only, again respected.* One
   `lake build` of this lane's was killed mid-flight (verified through
   `ps -o ppid` up to this session's own pid) because the next edit
   invalidated everything it was elaborating. No sources were edited
   under an in-flight build.


## L15 — THE RE-PIN LANDS: `bound_depth.lean` is a theorem about TODAY's engine again, and the blast radius was four files wider than priced (2026-08-19)

§L13 measured the fixture drift and found the re-pin BLOCKED; §L14 landed the
closure cells that unblocked it and priced what remained: *"what it costs is
`bound_depth.lean` … the blast radius is `bound_depth.lean` plus the
`sunfish.json`/`sunfish.py` pin — one file of theorems, not the directory."*
The re-pin is done and the header claim is retired. **The pricing was wrong in
one direction and right in another**, and both halves are worth recording.

### The fixture

`Examples/python/sunfish/sunfish.py` is engine master `e670434`, `sha256
f6c481a6a2c9f4c3686c13115adb36719693676d47b0121af03347d3a01219a1`, extracted
under `python3.9` (3.9.19 — the pinned frontend). `pins_common.lean` carries
the pass-8 re-extraction log; the drift header `bound_depth.lean` had been
carrying since §L13 is replaced by the re-pinned claim.

### What the re-pin actually touched

| file | why |
|---|---|
| `bound_depth.lean` | the whole point: §0 re-projected at 18, §3 re-derived, §6 wired, §7 re-measured |
| `sunfish.py` / `sunfish.json` | the fixture |
| `pins_common.lean` | the envelope trap's required real edit |
| `spec.lean` | **the genexp census** — 7 lowered genexps, indices `0,1,3,4,5,6,7` |
| `pins_init.lean` | **the module-globals census** — three new scalars |
| `init_chain.lean` | **78 pinned SPANS** at the padding-loop lambda, and 61 `<genexpr@n>` NAMES |
| `pins_bound.lean` | 14 of the 23 CPython pairs moved |
| `pins_search.lean` | the empty-trace frontier MOVED (below) |
| `pins_clock.lean` | the same, at search scale |
| `proof.lean` | envelope note (its own `load_program`) |

So: **nine Lean files plus the fixture pair, not one.** §L14's estimate was measured over THEOREMS and it
was right about those — every theorem in the generator tier
(`genmoves_ray`/`_scan`/`_drain`/`_theorem`, 3740 + 1156 + 326 + 563 lines) and
every theorem in `init_chain` re-elaborated green with no edit to a proof. What
it did not price is that a re-pin's real cost is in the **census and battery
`#guard`s**, which are pinned CONCRETE VALUES and move whenever the program
does — spans, synthesized names, node counts. The lesson generalizes: *a
drift-proof theorem is not a drift-proof file.*

### §0 — the eighteen statements, and the four that are new

`Searcher.bound`'s body census, pinned as a length (`sbB_length : sbB.length =
18`) so 13 → 18 can never be silent again:

| # | statement | |
|---|---|---|
| 0–5 | docstring, `nodes += 1`, the clock guard, `depth = max(depth,0)`, the king-capture check, the probe block | byte-identical to pass 7's, spans aside |
| 6 | `killer = self.tp_move.get(pos)` | NEW |
| 7 | `def moves()` | five captures, `guard` CELLED |
| 8–11 | `calm`, `guard`, `t`, `nmr` | NEW — the calmness test #236 lifted out of `moves()`, its root-excluded twin, and the deep-null fuel probe |
| 12–17 | `best, live = …`, the fold, the correction, the store, the eviction, `return best` | store/eviction/return byte-identical |

Every pin is project-and-pin (`nth n sbB`, then `∃ spans, … = shape := ⟨…,
rfl⟩`); no big-literal `rfl`, one statement per pin. Two pins are new kinds:
`sbDef_captures` pins `#["depth", "gamma", "<cell>guard", "killer", "pos"]` —
the cell's directory key as the tier's own object — and `sbCapPass_lit` pins an
`Expr.namedExpr`, §L14's walrus constructor, in general expression position.

### §3 — the fold vocabulary is a different program, and it has TWO terminals

Pass 7's `moves()` handed the consumer a finished `(move, score)` and the fold
was a walk over scores. #236 turned the pair around — `(value, move)`, both
`None` for a virtual yield — and moved the SCORING into the loop, across five
branches. The re-derivation makes the classification explicit:

* `Round` — `report (score) (live)` for the four scoring branches, `settle
  (cap)` for `if cap < gamma: best = max(best, cap); break`;
* `Exit` — `ran` / `cut` / `settled`, because the loop now has two ways to
  leave early and they are not interchangeable: a settled round folds its cap
  with `max`, sets NO `live`, and skips the cutoff block entirely (so it
  stores no killer);
* the five branches named as constructors (`standPat`, `cappedPass`,
  `searchedPass`, `intrinsicMate`, `searchedMove`/`settledCap`), each read off
  its own §0 pin;
* `moveCap` and `moveDepth` with their QS specializations, and `bit` for
  CPython's boolean-in-arithmetic coercion.

`foldFrom_nil`/`_cons_next`/`_cons_cut` survive in shape; `foldFrom_cons_settle`
is new and is an `rfl` — the settled arm takes NO hypothesis about `gamma`,
because `cap < gamma` was already decided when the round was classified.

### The finding §3 produced: depth 0 recurses into ITSELF, and that is what the QS gate is dodging

`moveDepth depth lmr nmr = depth - 1 - bit lmr - bit nmr`, and the child
refloors with `depth = max(depth, 0)`. Two theorems, one line each:

* `child_depth_lt` — at every `depth ≥ 1` the child's KEY depth is strictly
  below the parent's, for every reduction the code can apply (and
  `pass_depth_lt` / `nmr_depth_lt` for the two null probes at `depth - 3` and
  `depth - 7`). This is exactly the `d ≠ e` side condition
  `Bracket.SubtreeWrites` needs, discharged once for the whole tier.
* `qs_child_depth_eq` — at `depth = 0` it is `max (-1) 0 = 0`: **a QS node's
  children store under the QS node's own key.** The depth-separation arm does
  not cover them at all.

So the QS gate's `gamma ≤ pos.score` hypothesis is not a convenience — it is
what makes the fold CUT before any child runs, which is the only reason a
depth-0 statement can avoid the table question entirely. §L10 chose the
cleared-table form for the model's sake; this says the depth-0 case would have
needed it anyway.

### §6 — the table lines, wired to `DictCalc`, and it cost five theorems

§L13 built the calculus in the general layer *"precisely so that a re-pin would
not touch it"*, and this is the receipt. The three lines it models — the probe,
the store, `Entry = namedtuple("Entry", "lower upper")` — are byte-identical
between the two fixtures (measured span-blind before anything was written), so
the wiring is instantiation and nothing else: `sfBracket := tpBracket`,
`entryDefault`/`tpKey`/`entryOf` as the shipped values, then `sf_probe`,
`sf_store`, `sf_subtree_probe`, `sf_subtree_tableAt` — four one-to-three-line
consequences of `TableAt.get`/`.store`/`SubtreeWrites`. `entryBounds_entryOf`,
`entryBounds_default` and `pairKey_tpKey` are `rfl`. **`DictCalc`'s choice-free
axiom set is preserved through the wiring**: all four wired theorems print
`[propext, Quot.sound]`, no `Classical.choice`.

### The near-miss: a sixth attribute, and the gate that would have been vacuous

`Searcher.__init__` on engine master is `self.nodes, self.deadline, self.soft =
0, 1 << 63, 1 << 63` — SIX attributes, not five. `searcherObj` was carried over
at five, and it TYPECHECKED: `bound_enters` and `QSStandPat` would have been
perfectly good theorems about a receiver shape the engine never builds. It was
caught by reading `search()`'s new `if time.time() > self.soft: return` line,
not by the build. The repair is one field plus a `#guard` that matches
`searcherObj` against a real `Searcher()` over the real `initWorld` — the
non-vacuity check that would have caught it, now standing.

### The empty-trace frontier MOVED, and it got cheaper

Pass 5/6 pinned the wall at node 2048: nothing consulted `time.time()` below
it, so `pins_search` could step the driver four times at the empty trace.
Engine master ends every depth iteration with `if time.time() > self.soft:
return`, so the driver consults the wall once per COMPLETED DEPTH. At the empty
trace the fourth step now refuses — at 45 nodes, not 2048 — with the same
underrun message at the new consultation point. Both halves are pinned
(`pins_search.lean`: three yields, then the refusal). The frontier is a
statement about the PROGRAM, and it moved with the program.

### The batteries: 15 of 23 pairs moved, and TWO of them changed value

Every expected pair was re-derived by importing engine master's `sunfish.py`
into CPython 3.9 and probing it directly — the oracle, not the model. The model
then agreed on every row.

* **Twelve rows kept their value and lost nodes.** The settled-cap break
  leaves a sorted stream earlier: `posH 40 3` is `(39, 208) → (39, 197)`,
  `posEnd 60 3` is `(137, 27) → (137, 13)`.
* **The two TACTICAL rows changed value outright**: `posTac` answered exactly
  `MATE_LOWER = 47923` at depths 2 and 3 under pass 7 — the king-capture
  sentinel path — and engine master answers `277` and `417`. The futility cap
  settles the position before the mate line is searched. The board no longer
  exercises the sentinel discipline it was chosen for; recorded, not repaired.

### The empty-trace frontier at search scale, and what the seeded pin costs now

`pins_clock`'s deep-stepping pin had a matching shape change, and the new
consumption schedule IS the pin's content. Under a four-reading trace the
driver spends them at exactly four places, all measured on one pass:

| between | why | trace after |
|---|---|---|
| steps 3 → 4 | depth 1 converged (`self.soft`) | 3 left |
| steps 7 → 8 | depth 2 converged | 2 left |
| step 13 | depth 3 converged **and** node 2048 crossed inside `bound()` | 0 left |

Depth 3 now needs FIVE probes to converge where pass 7 needed four, so the walk
is 13 steps, not 12, and depth 4's first yield is `(4, 33, 32, g8f6)` at 2053
cumulative nodes. Every tuple and every node count is CPython's, checked
directly; the model reproduced all fourteen rows exactly.

### Triad, cold on the merged tree

`lake build` **3678 jobs green**, zero `sorry`/`admit`/`native_decide` and zero
`sorryAx`; the axiom profile over the whole tree is exactly three shapes —
307 `[propext, Classical.choice, Quot.sound]`, 20 `[propext, Quot.sound]` and
7 `[propext]` — and **`DictCalc`'s choice-free set is intact** (12 + 2 of its
own, plus the six §6 wirings, which land in the choice-free bucket rather than
widening it). The two expensive re-derived batteries dominate: `pins_bound`
1111 s and `pins_clock` 1091 s, both re-elaborated from scratch (against
§L13's `pins_clock` 917 s — the extra is depth 3's fifth probe and depth 4's
2053 nodes). `diff_test` **1315 cases, 0 failed, 113 whitelisted-unsupported,
1202 matched** — byte-identical to §L14's, so the fixture swap cost the
differential nothing. `docs_check` 71 marked blocks, 71 ok, 15
illustrative-exempt.

### Findings worth carrying

1. *A drift-proof THEOREM is not a drift-proof FILE.* Every theorem in the
   §L4–§L13 generator tier re-elaborated green with no edit — §L14's estimate
   was right about proofs. What moved was 78 pinned spans, 61 synthesized
   `<genexpr@n>` names, three censuses and 15 battery pairs. Price a re-pin by
   its `#guard`s, not by its `theorem`s.
2. *A carried-over receiver shape is the quietest way to lose a gate.* Adding a
   sixth attribute to `__init__` cannot break a build: it makes every statement
   ABOUT that shape vacuous. Any hand-written projection of a runtime object
   needs a `#guard` matching it against the real thing, and that guard belongs
   next to the definition, not in a battery file.
3. *Two terminals need two constructors.* Modelling #236's `break` as "a cut
   with a different score" would have typechecked and lost three facts at once
   (no `live`, no killer store, no look-ahead). The `Exit` enum costs one
   `deriving` line and makes `foldFrom_cons_settle` an `rfl`.
4. *A shared counter shows up as a GAP in a census, and the gap is evidence.*
   `<genexpr@2>` is absent from `sunfish.functions` because `genExpName` and
   `yieldFromName` draw from one counter in `Json.lean` and index 2 went to the
   `<yieldfrom@2>` loop target for `yield from sorted(…)`. Pinning the gap with
   its explanation is worth more than renumbering to hide it.
5. *When a battery moves, re-derive from the ORACLE.* All 23 pairs were taken
   from CPython on engine master, not from the model's own `#eval` — which is
   what makes "the model agreed on every row" a check rather than a tautology.
   The two tactical rows are why: a model-derived re-pin would have recorded
   `277` just as confidently and proved nothing.
6. *OPS — kills by PID and parentage only, and one edit-under-build slip
   recorded.* Four of this lane's own jobs were killed mid-flight (a `lake
   build` whose battery values were known-stale, two redundant duplicate
   evaluations, and a `diff_test` that had started a full build before
   `pins_clock` was re-pinned), each verified through `ps -o ppid` up to this
   session's own shell before the signal. **One slip against "never edit
   sources mid-build":** a COMMENT-only correction (a miscounted "fifteen of
   23" → "fourteen") was applied to `pins_bound.lean` while a standalone
   `lake env lean` of that same file was in flight. The values were untouched
   and the file was re-elaborated from scratch in the final triad, so nothing
   rests on the interrupted run — but the rule is about the dependency set, not
   about whether the edit looks harmless, and the discipline is cheaper than
   the audit.
7. *Re-deriving a battery is two full evaluations, not one, unless you plan
   it.* A failing `#guard` costs the same kernel run as a passing one and tells
   you nothing but "no". The cheap route is `#eval` with `IO.println` per row
   (output flushes as the walk proceeds) or — cheaper still — the CPython
   oracle, which answered all 23 pairs in under a second and was the thing the
   `#guard`s should agree with anyway.


## L16 — THE RECURSION RULE'S ARITHMETIC LANDS, and the futility break turns out to be a PREMISE, not a step (2026-08-19)

§L10 (c) wrote the rule's shape — *an induction hypothesis at depth `d-1`
consumed one round at a time at depth `d`* — and §L13 §8 paid its TABLE half in
the general layer. §L15's re-pin made the fixture current again. What was still
unwritten is the rule itself, and it has two halves that are not the
interpreter: **what the fold does to a child's REPORT**, and **what the composed
statement is**. Both landed. A third thing landed that was not on the list: the
general layer's child-subtree relation could not be instantiated at the shipped
code at all, and the theorems standing on it were vacuous.

### The vacuity, found by reading the relation against a real call

`Bracket.SubtreeWrites` (§L13 §8) had three arms: a bracketing store at the
table's own slot keyed at another depth, a write at any other slot, and `nil`.
Read against an actual `Searcher.bound` child that is not enough — a child
ALLOCATES on every visit (the `moves()` generator object, the `sorted(...)`
list), and `Heap.update` describes a write at an existing slot, never an
append. So the relation was true, `probe_stable` and `tableAt` were proved, and
**nothing in the shipped program could ever be shown to satisfy it.** Green and
meaningless, exactly the class §L15 finding 2 recorded for the sixth attribute.

The repair is one arm, `alloc`, with `a ≠ b` — the table is not the fresh
address — as its side condition. That condition is real and not a formality:
at `a = h.size` the same append turns a dangling probe into a live one, and
§9's new `#guard`s pin both halves against a one-slot heap.

`trans` came with it: `SubtreeWrites` is already a chain, so `n` children
compose to ONE subtree by append and a move fold needs no third theorem.

### The choice-freedom nearly went, and the culprit is a core lemma

Both new arms read the slot across a `push`. The obvious route is
`Heap.get?_push_of_get?` (PayloadBlind), and it made `probe_stable` and
`tableAt` print `[propext, Classical.choice, Quot.sound]` — DictCalc's
choice-free contract broken by a lemma nobody had printed. The cause is
**`Array.getElem?_push`, which depends on `Classical.choice`**, where
`Array.getElem_push_lt` depends on `propext` alone. The new
`Heap.get?_push_ne` is proved from the `dif` instead, is strictly more general
(a probe carries no liveness hypothesis, so it must cover the `none` answer
too), and is `[propext]`. DictCalc's profile is intact: 13 theorems at
`[propext, Quot.sound]` or less, `trans` at `[propext]`.

Its size arithmetic is by name and not by `omega`, for AGENTS.md's `PyInt`
reason one type down: **`Addr` is a reducible abbrev of `Nat`**, so a
comparison headed at it is skipped wholesale and `omega` answers "no usable
constraints found" with the constraint in plain sight.

### §7 — the rule's spec side, 31 declarations and no interpreter

* **The contract.** `Report` is `formal/Sunfish/CappedNull.lean`'s
  `WindowReport` restated verbatim (the lane depends on no package, so a
  bridge is a rename), with `negate` and `cap` — together they are
  `min(cap, -self.bound(…))` — and **`report_iff_docstring`**, which proves the
  predicate IS the shipped docstring's own two-implication promise. The
  docstring keys on where the VALUE sits and `Report` on where the REPORT
  sits; the equivalence is what says the lane proves the promise the engine
  makes rather than a neighbouring one.
* **Why a null window composes.** `Sound gamma value x := x < gamma ∨ x ≤
  value`. A child that fails HIGH at `1 - gamma` negates to at most `gamma -
  1` — strictly below the parent's window, a number it can never fail high on;
  a child that fails LOW negates to a genuine lower bound. Both land in
  `Sound`, `Sound` is closed under `max`, and `max` is the whole fold.
* **Five inductions over `foldFrom`** (`_sound`, `_ge`, `_cut_ge`, `_ran_ge`,
  `_settled_ge`) turn that into `fold_failHigh` — free, no exhaustiveness, no
  depth — and `fold_failLow`, which costs two premises. `fold_report` is the
  two assembled: the shipped contract at one node, from a classified schedule.
* **Consuming the IH.** `searchedMove_sound` (branch 5b) and
  `searchedPass_sound` (branch 2) are the two branches that call `bound`;
  both go `negate` then `cap`, which is `formal/`'s `cappedNull_report` at the
  parent's window. `report_sound` covers branches 1 and 4. Branch 3 and branch
  5a need NOTHING — both fire under a shipped guard `cap < gamma`, so both are
  `Sound` by the LEFT disjunct.
* **The table beside the frame.** `LoopFrameAt` generalizes §3's QS-specialized
  `LoopFrame` (which pins `depth = 0`, `nmr = false`) to any depth —
  `loopFrame_eq` is `rfl`, so no §3 statement moved — and `FoldInv` is the two
  halves in one proposition, with `LoopFrameAt.bindYield` (the loop target
  disturbs no slot) and `FoldInv.subtree` (a child disturbs no invariant).
  That is §L13's owed item 3, "TableOK threaded through the fold beside
  LoopFrame", spelled. `sf_body_tableAt` is the whole body — children, then
  the node's own store — and `sf_rounds_probe` is `trans` at the shipped slot.
* **`BoundRefines`**, the depth-indexed statement, stated in the manner of §5's
  `QSStandPat`, and `RecursionStep`, the step it owes.

### THE FINDING: `bound_refines_fuelModel` is FALSE without a futility premise

`settle_needs_futility` is a theorem, not a caveat. It exhibits a schedule —
window 100, value 50, a settled cap of 10 ahead of a round worth exactly 50 —
in which every round is `Sound`, the value IS attained by the schedule, and
the fold still answers **10**: neither a lower bound (it is below the window)
nor an upper one (the value is 50).

So the refinement statement needs a side condition, and the shipped code's own
justification for it is the comment on the break — *"the stream being sorted,
[the cap answers] for everything after it"* — which is a property of `moves()`'s
ORDERING and not of the fold. The fold cannot supply it; `hfut` is where it
enters. Two `#guard`s make the point concrete: the same two rounds with the
settle SECOND answer 50, the value. The fold sees only the order.

The same shape recurs one level down and is recorded at `searchedMove_sound`:
`hneg : -childValue ≤ value` is not the textbook negamax inequality, because
the child is searched at `moveDepth depth lmr nmr` and not at `depth - 1`. It
holds because the docstring DEFINES `s*` to include *"null moves, QS, futility
and the reductions"*. A model whose value is the unreduced negamax owes `hneg`
a proof, not a definition — which is the first thing a bridge to `formal/`'s
`fuelValueD2` has to check.

### Non-vacuity, measured on the ENGINE — and it pins two values exactly

`Report` is a claim about a value function this file does not compute, so the
check is CONSISTENCY: `bd_claim` runs the shipped `bound` at several windows on
one key and intersects what the answers claim — a fail-high report is a lower
bound on `s*`, a fail-low report an upper bound. A row that cannot run answers
with the EMPTY interval, so a broken probe can never look consistent.

| key | windows | reports | interval |
|---|---|---|---|
| opening board, depth 0 | −100, −40, 0, 1, 40 | 0, 0, 0, 4, 4 | **(4, 4)** |
| opening board, depth 1 | 0, 20, 37, 40 | 0, 37, 37, 37 | **(37, 37)** |

Nine independent searches, and at each key the reports agree to the integer:
the shipped code's own answers determine `s*(opening, 0) = 4` and
`s*(opening, 1) = 37`. That is what a satisfied `Report` looks like on real
numbers, and it is a differential check rather than a tautology because the
value never came from the model.

### What landed

| file | what |
|---|---|
| `LeanModels/Python/PayloadBlind.lean` | `Heap.get?_push_ne`, choice-free (+28 lines) |
| `LeanModels/Python/DictCalc.lean` | `SubtreeWrites`'s `alloc` arm, `trans`, 6 `#guard`s (+79 lines) |
| `Examples/python/sunfish/bound_depth.lean` | §7, the recursion rule; §7→§8 renumber (+530 lines) |

**31 new declarations** in `bound_depth` (23 theorems, 7 `def`s, one private
helper), **16 new `#guard`s**, **24 new `#print axioms`**. Every new theorem
prints `[propext, Classical.choice, Quot.sound]` or less; `settle_needs_futility`,
`foldFrom_cut_ge`, `LoopFrameAt.bindYield` and `Heap.get?_push_ne` are
`[propext]`, and `report_sound`/`cappedPass_sound`/`settledCap_sound`/
`loopFrame_eq` depend on no axioms at all. No `sorry`, no `native_decide`.

**Triad, both commits:** `lake build` **3678 jobs green**; `docs_check` 71
marked blocks, 71 ok, 15 illustrative-exempt; `diff_test` **1315 cases, 0
failed, 113 whitelisted-unsupported, 1202 matched** — byte-identical to §L15's,
so neither change touched the differential; `script_corpus` 64 scripts, 0
failed, 50 matched, 14 loud. The DictCalc edit re-elaborated the whole tree
(`pins_bound` and `pins_clock` 1108 s each, against §L15's 1111/1091 — flat).
`bound_depth` itself went **58 s → 3 m 15 s**, all of it the nine added real
searches.

### Findings worth carrying

1. *A relation with the wrong arms is the quietest vacuity there is.* A missing
   CONSTRUCTOR cannot break a build, cannot break a proof, and cannot be seen
   in an axiom print — it just means nothing in the program inhabits the
   relation. §L15 caught a receiver shape by reading `__init__`; this was
   caught by reading `SubtreeWrites` against what a `bound()` call actually
   does to the heap. **Read every inductive's arms against one real execution
   before proving anything over it**, and prefer a `#guard` on the underlying
   computation to a proof about the relation.
2. *Print the axioms of the LEMMAS, not only of the theorems.* DictCalc's
   choice-freedom was broken by `Array.getElem?_push` two levels down, through
   a PayloadBlind lemma that had never been printed. A contract about an axiom
   set is a contract about a transitive closure.
3. *A premise that the code justifies in a COMMENT is a premise.* The futility
   break's soundness rests on `moves()`'s sort order, the reductions' on the
   docstring's definition of `s*`. Both are true and neither is a step of the
   fold; a refinement theorem that omits them typechecks and is false
   (`settle_needs_futility` is the witness). Name them as hypotheses at the
   site that can pay them — §L13 finding 2's rule, applied to arithmetic
   instead of a table.
4. *The consistency sweep is the cheapest non-vacuity instrument this lane
   has.* Nine `#guard`s over the real engine pinned two exact values without
   the file computing a single one of them, and they would fail loudly if the
   contract were violated at either key. It costs one `bd_probe` per window and
   it checks the THEOREM's predicate, not the theorem's proof.
5. *OPS — one slip against "never edit sources mid-build", recorded.* §7 was
   written into `bound_depth.lean` while the tree-wide `lake build` triggered
   by the DictCalc edit was still running, and lake read the half-finished file
   when it reached that job. Nothing rests on the interrupted run — the errors
   it printed were from a snapshot that no longer exists, `bound_depth` is not
   in any other job's dependency set, and the final triad rebuilt it from
   scratch — but the rule is about the dependency set and the discipline is
   cheaper than the audit. §L15 finding 6 recorded the same slip; twice is a
   pattern, and the fix is to stage the edit and start the build after it.
6. *`pgrep -f "lake build"` matches its own waiter.* An `until ! pgrep -f "lake
   build"` loop never terminates, because the loop's own command line contains
   the pattern. Two waiters spun for the whole session before `ps -eo
   pid,comm | grep lean$` answered the question in one line. Match on the
   process NAME, never on a command line the watcher itself contains.

### What step 3 still owes

§L13's list, updated. Items 1 (closure cells) and 2 (the re-pin) landed in
§L14/§L15; item 3 is now half paid.

1. **The interpreter half of `RecursionStep`** — §L10's step-2 items 1–5, at
   the measured unit cost of one `py_simp` per statement with its module-level
   residues pinned. This is the whole remaining cost, and it is a known
   quantity: the probe block, the mate check, the nested `def` and `moves()`,
   the fold via `PyStmtTriple.forGen`, and the tail.
2. **`QSStandPat`**, which the same gates close, and which is the base case.
3. **The futility premise itself** — either as a hypothesis carried into
   `bound_refines_fuelModel` (honest, and what `hfut` already is), or as a
   theorem about `moves()`'s sort order, which is a statement about the
   generator this lane has already proved a great deal about
   (`gen_moves_drains_ref`, `sf_order`). The second is the better answer and
   nobody has priced it.

**`model_audit` cannot retire yet, and the report should say so plainly.** What
retires it is a proved `bound_refines_fuelModel`, and that needs item 1. What
this pass changes is that the statement is now WRITTEN (`BoundRefines`), every
non-interpreter ingredient is proved, and the two side conditions it must carry
are named rather than discovered later.


## L17 — THE INTERPRETER HALF OPENS: eleven of eighteen statements have gates, and the wall is `evalExpr` at a symbolic operand (2026-08-19)

§L16 paid the recursion rule's spec side and named the remaining cost as *"the
interpreter half of `RecursionStep`"* — §L10's step-2 items 1–5, one `py_simp`
per statement. This pass ran that list in order. **Eleven of the eighteen
statements now have an interpreter gate**, `QSStandPat` does NOT close, and the
pass produced one measurement that corrects a recorded assumption and one wall
whose diagnosis was not what the roadmap expected.

### The gates, and what §L10's price turned out to mean

| # | statement | gate |
|---|---|---|
| 0–2 | docstring, `nodes += 1`, the clock guard | `bound_enters` (§L10) |
| 3 | `depth = max(depth, 0)` | `depth_refloors` |
| 4 | the king-capture check | `mate_check_passes` |
| 5 | the probe block, four statements | `probe_misses`, `probe_lower_passes`, `probe_upper_passes`, `probe_repetition_skipped` |
| 6 | `killer = self.tp_move.get(pos)` | `killer_misses` |
| 7 | `def moves()` | **owed** |
| 8 | `calm` | **owed** |
| 9 | `guard = not root and calm` | `guard_evals` |
| 10 | `t = pos.score + NULL_MARGIN` | `null_margin_adds` |
| 11 | `nmr` | `nmr_evals` |
| 12 | `best, live = -MATE_UPPER, False` | `acc_inits` |
| 13 | the fold | **owed** |
| 14–17 | correction, store, eviction, return | **owed** |

§L10 measured the probe block at *"over 4M heartbeats as a single block"* and
concluded it was the expensive one. Split per statement the four gates
elaborate in about **3 s together**. So the measurement was right and the
conclusion was wrong: what it measured was not the work, it was the SHAPE. The
whole six-gate head batch is ~3 s; the file's total went 58 s → 3 m 21 s and
every second of the increase is `#guard`s running real searches, not proofs.

### Two residues, both §L9 finding 3's shape

* `pos.score` on a namedtuple-SUBCLASS value forks on `c.ntBase.isSome && attr
  ∈ c.methods` (methods shadow field properties, CPython's MRO). `Position` is
  projected once — `posCls`, `posCAux`, `posCls_methods` (five methods, `score`
  not among them), `posCls_ntBase_isSome` — and the guard is decided from the
  pinned ARRAY. **`posCAux` must be IN the simp set**: without it the surviving
  `match` is a different matcher constant from any hand-written one and no pin
  can fire, however exactly it is spelled.
* `entry.lower` needs `entryClsAux`: an attribute read consults the class table
  even for a plain namedtuple.

One tactic note: a `¬ P` passed in `py_simp`'s list does NOT reduce the `ite`
it is about. `rw [if_neg (show ¬ P by omega)]` does, and five gates use it.

### THE MEASUREMENT: `NULL_MARGIN` is not poisoned, and a recorded premise is redundant

§L15's `QSStandPat` carries `Env.lookup w.globals "NULL_MARGIN" = some (.int
nullMargin)` with the reasoning *"#236's `t = pos.score + NULL_MARGIN` runs
before the fold even at depth 0, so the name has to resolve."* It does have to
resolve — but it resolves STATICALLY. Measured on the fixture:

| name | static fold |
|---|---|
| `MATE_LOWER`, `MATE_UPPER` | `some none` — bound but dirty, live view decides |
| `NULL_MARGIN` | `some (some -200)` |
| `QS` | `some (some 40)` |
| `LMR` | `some (some 75)` |

So `null_margin_adds` says nothing about `w.globals`, and `QSStandPat`'s
`NULL_MARGIN` premise is **redundant**. It stays — AGENTS.md's rule is to keep
an unneeded hypothesis and record the fact, and a redundant premise only
weakens a statement — but the record is now in the file at `nmarG` and here.

### THE WALL, and it is NOT the recursion

`nmr = calm and depth >= 6 and -self.bound(...) >= t` dies on its SECOND
conjunct at every QS node, so the child never runs and the roadmap treated the
statement as cheap at depth 0. It is not, and the reason is instructive:

`py_simp` normalizes the UNREACHABLE branch. It unfolds `evalBoolChain` down to
`evalExpr sunfish _ st r`, where `r` is the opaque third operand `sbNmr_lit`
provides — and **`evalExpr` at a FREE SCRUTINEE splits into every arm of its
match, each carrying the 1MB literal.** Measured: 2 minutes to the simp STEP
budget at 8M heartbeats. The diagnostics are the tell — `imp_false` used 1242
times, `eq_self` tried 7868, `nonempty_prop` 634 — all generic propositional
lemmas, which is the signature of a goal that has exploded rather than of a
hard fact. Casing on the symbolic `calm` first does not help: the problem is
the third operand, not the first. Nor does the `t` lookup: supplying it changes
nothing.

**The fix is altitude, and it is cheap.** `boolChain_and_falsy` and
`boolChain_and3` prove the short circuit ONCE at the chain with every operand
symbolic — in `and3`, `e3` is universally quantified and appears in NO
hypothesis, so `evalExpr` is never applied to it. Neither lemma mentions a
module, a program or a fuel numeral; both are five lines. With them the gate is
**1.7 s**, from a two-minute failure. They sit in `bound_depth.lean` because
this is their first consumer and belong in the general layer at the second.

### Item 3, PRICED: the futility premise splits, and only half is a theorem

The brief asked whether `hfut` can become a theorem about `moves()`'s sort
order. Reading the shipped ordering line answers it in two halves.

* **(a) The sortedness half is provable.** The stream is descending in `val`
  and `moveCap` is monotone in `val`, so a cap under the window stays under it
  for every later move — the source's own *"the stream being sorted, [the cap
  answers] for everything after it"*. `moveCap_mono` and `moveCap_lt_of_tail`
  are that claim at the cap, landed. What remains is carrying it to the fold's
  TAIL, which needs the drained ordered list — an object `sf_order` produces and
  `gen_moves_drains_ref` specifies. A session's work in this lane.
* **(b) The per-move bound is not provable here.** Sortedness says the tail's
  CAPS are low; it does not say a cap bounds the tail's true VALUES. That step
  is `-V(child m) ≤ moveCap depth pos.score (value m)` — a property of the
  evaluation function against the search value, which no reading of `bound()`
  establishes. The shipped comment points at exactly this
  (`CapInBand in CappedMove.lean`, with its caveat about `piece["Q"]`).

**So "can `bound_refines_fuelModel` drop the futility premise" is YES BY
DEFINITION and NO BY THEOREM, and which holds is a choice about the MODEL.**
The docstring defines `s*` to include *"null moves, QS, futility and the
reductions"*; under that definition (b) is definitional and (a) is the whole
content. Against a model whose value is unreduced, unpruned negamax, (b) is a
genuine axiom and belongs in `formal/`. Either way the premise stays visible,
which is what `settle_needs_futility` bought.

### Triad

Both commits: `lake build` **3678 jobs green**; `docs_check` 71/71, 15
illustrative-exempt; `diff_test` **1315 cases, 0 failed, 113
whitelisted-unsupported, 1202 matched** — unchanged since §L15, so eleven new
gates cost the differential nothing; `script_corpus` 64 scripts, 0 failed, 50
matched, 14 loud. Every new theorem prints `[propext, Classical.choice,
Quot.sound]` or less; `boolChain_and_falsy`/`boolChain_and3` and
`moveCap_lt_of_tail` are choice-free. No `sorry`, no `native_decide`.

### Findings worth carrying

1. *A measured price is a price for a SHAPE, not for a quantity.* "Over 4M
   heartbeats" said the probe block could not be done in one `py_simp`; it did
   not say the block was expensive, and split per statement it is 3 s. Record
   the shape a measurement rules out, not the difficulty it seems to imply.
2. *A short circuit in the PROGRAM is not a short circuit in the PROOF.* simp
   normalizes the branch the interpreter never takes, so an unreachable
   subexpression is still a cost — and if it is symbolic, `evalExpr` at a free
   scrutinee makes it an unbounded one. The H3/H5 free-scrutinee findings were
   about the interpreter's own dispatch; this is the same fact one level up, in
   the PROOF's simp set. When a statement carries an operand you deliberately
   left opaque, prove the control flow at the CHAIN, never at the statement.
3. *Read the diagnostics, not the timeout.* `set_option diagnostics true` with a
   small heartbeat budget answered in 11 s what two 2-minute runs could not: a
   used-theorem histogram topped by `imp_false`/`eq_self`/`nonempty_prop` means
   the goal exploded, and points at a term simp should never have opened.
4. *A hypothesis can be wrong by being UNNECESSARY.* `QSStandPat`'s
   `NULL_MARGIN` premise was added from a correct reading of the source and a
   wrong assumption about the globals fold. It is harmless and it is still a
   defect in the record, because the next lane would have paid it. Measure
   which globals are poisoned before assuming the live view is needed.
5. *OPS — both §L16 fixes held.* Every build this pass was started AFTER `git
   add`, and no source was edited while a build ran; process checks used `ps
   -eo pid,comm | grep -E "lean$|lake$"`, never `pgrep -f "lake build"`. The
   scratch-file loop (`lake env lean` against a scratch file importing the
   built module) is what made a 3 m file iterable at 2 s, and it is the single
   biggest throughput win of the pass — 20+ iterations that would each have
   cost 3 m against the file itself.

### What is still owed, in order

1. **Statement 7, `def moves()`** — the closure allocation with the celled
   `guard` (§L14's tier), the `sunfish` analogue of §L9's
   `moves_def_allocates`/`moves_call_creates`. Mechanical, and the cell is the
   only new part.
2. **Statement 8, `calm`** — `abs(pos.score) < 750 and any(c in pos.board for c
   in "RBNQ")`. The heaviest of the head: `abs` and `any` residues plus a
   LOWERED genexp, so it needs its own `<genexpr@n>` census pin. Expect
   `boolChain_and3`'s sibling for the two-operand chain.
3. **Statement 13, the fold**, via `PyStmtTriple.forGen` with `qs_round` built
   from per-expression `EvalsTo` gates — §L10's item 4, unchanged, and now with
   §L16's `fold_report` waiting for it.
4. **Statements 14–17, the tail**, then the boundary, closing `QSStandPat`.
5. Then `RecursionStep`, and then `bound_refines_fuelModel` assembles.

**`model_audit` STILL CANNOT RETIRE, and this pass does not change that.** What
retires it is a proved `bound_refines_fuelModel`; `QSStandPat` is its base case
and four of the eighteen statements it needs are unpaid. What changed is that
the head is done, the fold's spec side is done, and the two premises the
statement must carry are named and half-priced.


## L18 — THE CELL IS SPENT ON THE SHIPPED FILE, `calm` NAMES ITS GENEXP, and the model choice is TAKEN (2026-08-19)

§L17 left statements 7 and 8 owed and everything else in the head paid. Both
landed. **Thirteen of the eighteen statements now have an interpreter gate**;
what remains is the fold and the tail.

### Statement 7 — `def moves():` allocates TWO objects, and the cell is empty

§L14 built the closure cells; this is the first time they are spent on the
shipped file, and the shape is worth recording. The captures are
`#["depth", "gamma", "<cell>guard", "killer", "pos"]` — four plain names and one
CELL DIRECTORY KEY — so `allocCells` pushes one `.cell none` and binds
`<cell>guard` to its address BEFORE the snapshot runs, and the snapshot then
carries a REF where a value would have been. The `def` therefore leaves **two**
heap objects where the snapshot tier left one.

**The cell holds `none`, and that is the point rather than a defect.** `guard`
is assigned at statement 9, below the `def` at 7, so at allocation time the name
has no binding — precisely the source order the snapshot tier refused outright
(§L13's blocker) and the cell admits.

`execStmt_nestedDef` (GenBound.lean) does NOT apply: its hypothesis is
`allocCells st caps = st`, i.e. no cells. `execStmt_nestedDef_cells` is the same
theorem with the post-allocation frame as its own variable, and the snapshot
version is its `st' = st` case — a strict generalization, so it belongs in
GenBound the moment a second consumer appears.

§L9 finding 4 cost exactly one parse error, as recorded: a structure-instance
field value may not continue on a less-indented line. `sbW1`/`sbW2`/`sbEnvDef`
are named partly for that and partly because the fold reads them.

### Statement 8 — the gate NAMES the genexp's answer

`calm = abs(pos.score) < 750 and any(c in pos.board for c in "RBNQ")`, and the
second conjunct ingests as `any(<genexpr@3>("RBNQ", pos))` — the head's one
lowered genexp. Its value depends on which piece letters the board carries, so
over a symbolic board it cannot be decided without four membership tests.

`calm_evals` carries it as ONE `evalExpr` premise instead, discharged per board,
and the chain's value IS it (`boolChain_and2`, the two-operand sibling of §L17's
lemmas). **That the premise can stay open is a fact about depth 0, not a
shortcut**: `calm` reaches the fold only through `guard`, and `guard` is read at
`2 < depth < 6` (the scoring null) and at `guard and depth >= 6` (intrinsic
LMR) — both false at a QS node. A depth-≥2 gate owes the genexp its own drain.

`abs` gets the five residues `max` already had. `<genexpr@3>` is pinned present
in the census by `#guard`, so the premise cannot come to be about a name the
ingestion no longer emits.

### THE MODEL CHOICE, TAKEN — and the pairing, explicit

§L17 split the futility premise into a provable sortedness half and an
unprovable per-move half, and left the statement's target open. **Decided as
default, pending Thomas's ratification:**

> `bound_refines_fuelModel` is stated against **the DOCSTRING's `s*`** — the
> promise `report_iff_docstring` pins, in which the per-move futility bound and
> the reduction bound are DEFINITIONAL, because the docstring defines `s*` to
> include *"null moves, QS, futility and the reductions"*. **`formal/`'s
> `CapInBand` (`formal/Sunfish/CappedMove.lean`) is the recorded axiom for the
> unreduced-negamax gap.** The two repositories then split the claim cleanly:
> **lean-surfaces proves that the code keeps its own documented promise;
> `formal/` carries the search-theory content that the promise is worth having.**

The premise STRUCTURE is deliberately untouched by the choice — `hneg` and
`hfut` are hypotheses under either reading — so the two readings are one
definition of `V` apart and an override is a rename, not a reproof.

### What landed

`bound_depth.lean` only: `execStmt_nestedDef_cells`, `guardCell`, `sbDef_cells`,
`sbMovesCap`, `sbMovesClosure`, `sbW1`, `sbW2`, `sbEnvDef`, `sbDef_snapshot`,
`moves_def_allocates`, `boolChain_and2`, `abs_score_evals`, `calm_evals`, the
five `abs` residues, four grounding `#guard`s and eight `#print axioms`. Every
new theorem prints `[propext, Classical.choice, Quot.sound]` or less;
`boolChain_and2` and `execStmt_nestedDef_cells` are choice-free.

**Triad:** `lake build` 3678 jobs green; `docs_check` 71/71, 15
illustrative-exempt; `diff_test` 1315 cases, 0 failed, 113 whitelisted, 1202
matched — unchanged since §L15 across thirteen gates; `script_corpus` 64
scripts, 0 failed, 50 matched, 14 loud. The file elaborates in 3 m 25 s, all of
the growth still the `#guard`s' real searches.

### Findings worth carrying

1. *A cell that holds `none` is the tier working, not failing.* The instinct on
   reading `allocCells`' `.cell (Env.lookup st.locals (cellName c))` at an
   unbound name is to look for the bug. There is none: the empty cell IS the
   admission of a capture assigned below its own `def`, which is the shape that
   blocked the whole re-pin until §L14.
2. *When a subexpression's value is irrelevant to the statement, make it a
   PREMISE and prove the irrelevance.* `calm_evals` does not decide the genexp;
   what makes that honest is the separate reading of where `guard` is consumed
   (`2 < depth < 6`, `depth >= 6`), both dead at depth 0. A premise without
   that reading would be a gap; with it, it is a factored proof.
3. *A generalization of a general-layer theorem is a general-layer theorem.*
   `execStmt_nestedDef_cells` subsumes `execStmt_nestedDef`. It sits locally
   only because moving it costs a tree-wide rebuild, and that is a scheduling
   decision, not a design one — recorded so the next lane merges rather than
   duplicates.
4. *The model choice was cheap because the premise structure was already
   right.* §L16 stated `hneg`/`hfut` as hypotheses at the sites that can pay
   them rather than folding them into the value function. That is why choosing
   the docstring reading is a definition swap and not a restatement — the same
   reason §L13 finding 2 gave for making an invariant clause a hypothesis.

### What is still owed

1. **Statement 13, the fold**, via `PyStmtTriple.forGen`, with `qs_round` built
   from per-expression `EvalsTo` gates — §L10's item 4. §L16's `fold_report` is
   waiting for it, and §L18's `sbW2`/`sbEnvDef` are the world and frame it
   starts from. This is now the single largest remaining piece.
2. **Statements 14–17**, the correction (dead at depth 0 — `sbCorr` is
   depth-gated), the store, the eviction's false guard and the return, then the
   boundary — which together close `QSStandPat`.
3. Then `RecursionStep`, and `bound_refines_fuelModel` assembles.

**`model_audit` CANNOT RETIRE YET.** Five of eighteen statements are unpaid and
`QSStandPat` is unproved. The head is complete, the recursion rule's spec side
is complete, both side conditions are named, and the statement's target is now
DECIDED — but the fold is not written and no assembly exists.


## L19 — THE FOLD LANDS, three quarters of the tail with it, and 17 of 18 statements are gated (2026-08-19)

§L18 named the fold as *"the single largest remaining piece"*. It is done, via
`PyStmtTriple.forGen`, and the three cheap tail statements came with it.
**Seventeen of the eighteen statements now have an interpreter gate.** The one
remaining is statement 15, the table STORE.

### The fold, and why one round is the whole proof

At a QS stand-pat node the shipped `for val, move in moves():` runs **exactly
one round and breaks**, and the engine says so at ONE node
(`bd_probe (posH 0) 0 0 == some (0, 1)` — a `#guard` that has stood since §L15
and is now what the gate is checked against).

The rule instantiation is where the economy is:

* **schedule `[qsY]`** — the virtual `(None, None)` the `depth == 0` clause
  yields, and nothing after it;
* **`QSInv` pins the frame AND the yield** (`| [y] => st = ⟨w₁, e⟩ ∧ y = qsY`).
  Pinning the yield is not decoration: `hstep` is quantified over every `x`, so
  an invariant that constrained only the frame would owe a round for a yield the
  generator never produces;
* **`Inv [] = False`** — the empty schedule is UNREACHABLE, because the fold
  breaks on round one. That makes `hexit` vacuous and leaves exactly ONE
  `hstep` obligation. A rule with three obligations collapses to one because the
  program never runs out of moves; it leaves early.

Two generator-side facts stay named premises — `hev` (the `moves()` call
allocating the object) and `hyield` (its first step) — which is the sf_order
precedent's own shape (`bound_body_returns` took its `hands` schedule the same
way).

### The body is paid, and the altitude fix earned its keep twice more

* `qs_score` — branch 1 fires and `score = pos.score`. The `elif` chain below it
  is four more branches, two of them recursive, and it is a **defined
  projection** (`sbElse1`), not an opaque variable — so `py_simp` would walk it
  and explode exactly as it did on `nmr`'s third operand.
  `execStmt_if_true`/`execStmt_if_false` keep it out by deciding the branch AT
  the `ifStmt`. §L17's finding, second and third applications.
* `qs_max` — `best = max(best, score)`, with `max (-MATE_UPPER) sc = sc`.
* `qs_cut` — the cutoff fires, and `kill_guard_false` gets **three facts from one
  guard**: `move is not None` is false on a virtual yield, so the `and` never
  reaches `depth`, the killer is not stored, the eviction inside the cutoff is
  never reached, and the QS fold is heap-free. All three were assumptions in
  §L10's `LoopFrame` docstring; now they are one lemma.

`execStmt_mono` composes the three at their own fuels — no threshold plumbing
needed — and `PyTriple.of_exec` lifts the `.brk` run into the triple the rule
wants.

### The bridge, and it is one line

`qs_fold_agrees`: `foldFrom gamma (-mateUpper) false [standPat sc] = (sc, false,
.cut)`. The interpreter's answer IS §3's fold, so §4's gates and §7's
`fold_report` are now connected rather than merely adjacent. Without this line
the fold would typecheck and mean nothing — it is the same discipline the
`report_iff_docstring` equivalence applies to the contract.

### The tail: three of four

* `corr_dead` — the correction is DEAD at depth 0, because `depth` is the FIRST
  conjunct of `depth and not live and all(…)` and a falsy `0` short-circuits
  before the `gen_moves()` scan. `boolChain_and_falsy`, third application. It
  needed a sharper pin: `sbCorr_lit` left the `else` arm existential and a dead
  branch has to REDUCE, so `sbCorr_noElse` records that the shipped correction
  has no `else`. The old pin is untouched.
* `evict_dead` — the eviction never fires, stated over a FREE entry array with
  `es.size ≤ TABLE_SIZE` rather than at one entry, so the same gate serves every
  depth. `TABLE_SIZE` resolves statically (like `NULL_MARGIN`, §L17), so the gate
  says nothing about `w.globals`; `len` gets the five residues `max`/`abs` had.
* `ret_best` — `return best`, in the `.ret` arm.

### Triad

Both commits: `lake build` **3678 jobs green**; `docs_check` 71/71, 15
illustrative-exempt; `diff_test` **1315 cases, 0 failed, 113 whitelisted, 1202
matched** — unchanged since §L15 across seventeen gates; `script_corpus` 64
scripts, 0 failed, 50 matched, 14 loud. Every new theorem prints `[propext,
Classical.choice, Quot.sound]` or less; `execStmt_if_true`/`_if_false` are
choice-free. No `sorry`, no `native_decide`.

### Findings worth carrying

1. *A loop that LEAVES EARLY is cheaper to verify than a loop that finishes.*
   `Inv [] = False` turns `PyStmtTriple.forGen`'s three obligations into one,
   because the exit obligation is about a state the program never reaches. When
   a loop provably breaks, choose the schedule that ends where the break does
   and let the invariant refute the rest — do not prove the tail you never run.
2. *An invariant over a quantified element must pin the ELEMENT.* `hstep` ranges
   over every `x`; an invariant constraining only the frame would have owed a
   round for a yield `moves()` never produces. One extra conjunct (`y = qsY`)
   is the whole fix, and its absence would have shown up as an unprovable
   obligation rather than as a false theorem — but only after the work.
3. *An existential pin is a liability wherever a branch must REDUCE.*
   `sbCorr_lit`'s `oe : Array Stmt` is right for a census and wrong for a dead
   branch: `execStmts _ oe.toList` cannot step. Pin the shape you will need to
   COMPUTE with, and add the sharper pin rather than weakening the recorded one.
4. *One guard can be worth three facts.* `kill_guard_false` is why the QS fold
   stores no killer, never reaches the eviction, and is heap-free — three
   properties §L10 asserted separately in prose. Look for the single decision
   that discharges a cluster of assumptions.
5. *A linter can be wrong about which simp argument did the work.*
   `simp only [Run.bind]` twice in `qs_body` is flagged unused and is not:
   removing either leaves the next `rw` without its pattern. Measured both ways,
   silenced on that theorem with the reason recorded — never by deleting the
   step and hoping.

### What is left

1. **Statement 15, the table STORE** — `self.tp_score[pos, depth] = Entry(best,
   entry.upper) if best >= gamma else Entry(entry.lower, best)`, the only tail
   statement that changes the heap. §6's `sf_store` is the invariant half,
   already proved; what is owed is the interpreter run — the conditional
   expression, the `Entry(…)` construction and the `heapStore`.
2. **The boundary**, and `QSStandPat` closes.
3. Then `RecursionStep`, and `bound_refines_fuelModel` assembles.

**`model_audit` CANNOT RETIRE YET** — but the distance is now one statement plus
the boundary, where at the start of §L17 it was seven statements plus the fold.


## L20 — EIGHTEEN OF EIGHTEEN, the two halves MEET, and the last step is a composition (2026-08-19)

§L19 left statement 15 and the boundary. **Statement 15 landed, so every
statement of the shipped `Searcher.bound` now has an interpreter gate**, and the
three sections that were built separately are joined. `QSStandPat` does NOT
close: what is left is the COMPOSITION, and this pass measured what that costs
and removed its blocker.

### Statement 15 — the store, and the shape a gate must have

`self.tp_score[pos, depth] = Entry(best, entry.upper) if best >= gamma else
Entry(entry.lower, best)`. At a stand-pat node the conditional takes its
fail-high arm, so what lands is `Entry(pos.score, MATE_UPPER)`.

Two mechanical findings, both about SHAPE rather than difficulty:

* The gate concludes with the **computed heap**, not an abstract `h'`. The
  subscript-store path inlines past `heapStore` into `Heap.update`'s `dif`, and
  `-heapStore` does not stop it, so a `heapStore` premise cannot match what
  `py_simp` leaves. `bound_enters` took a `Heap.update` premise for the same
  reason in §L10 — the precedent was there and was rediscovered rather than read.
* The two `Array.set` terms then differ only in their liveness PROOF. Proof
  irrelevance closes it: one `rfl`.

### WHERE THE TWO HALVES MEET

`sf_store_from_report`, §7. Two theorems had been waiting for each other:

| proved | since | needed | had |
|---|---|---|---|
| `sf_store` (§6) | §L15 | `lo ≤ V p d ∧ V p d ≤ up` | nothing to discharge it |
| `fold_report` (§7) | §L16 | — | `Report gamma best (V p d)`, nothing to give it to |

The join is one `rcases`: **a fail-high report IS the lower bound the store's
entry claims**, because `gamma ≤ best` forces `Report`'s right disjunct. With
`store_runs` (§4) putting the entry there, three sections close a circle — the
code stores a bound, the fold proves it is one, the calculus keeps the table's
invariant across it. `hband` (`V p d ≤ MATE_UPPER`) stays a premise: the mate
band is a fact about the value function, not something a store can establish.

### The composition's blocker was the gates' own shape

`probe_block_runs` composes the four probe statements plus the `if not root:`
wrapper into one gate. The obstacle was not the statements — it was that **every
gate is stated over a one-statement LIST** (`execStmts sunfish F st [s]`), which
is the shape a reader wants and the wrong shape for composition, because
`execStmts` peels one statement at a time and chaining needs `execStmt`.

`execStmt_of_singleton` is the conversion, and with it the composition is four
`rw`s instead of a page of bookkeeping. **State the next batch at `execStmt` and
let the singleton form be the corollary.** `execStmt_if_true`/`_if_false` moved
up to sit beside it — general, and needed by the probe wrapper before the fold.

### Triad

Both commits: `lake build` **3678 jobs green**; `docs_check` 71/71, 15
illustrative-exempt; `diff_test` **1315 cases, 0 failed, 113 whitelisted, 1202
matched** — unchanged since §L15 across all eighteen gates; `script_corpus` 64
scripts, 0 failed, 50 matched, 14 loud. Every new theorem prints `[propext,
Classical.choice, Quot.sound]` or less. No `sorry`, no `native_decide`.

### What `QSStandPat` still needs, priced

The gates are all there; the boundary is an assembly job with three named
premises. In order:

1. **The frame chain.** Eighteen gates, each stated over a frame satisfying a
   handful of `Env.lookup` facts, composed through an `Env.set` chain that grows
   at statements 3, 5, 6, 7 (twice), 8, 9, 10, 11, 12 and inside the loop. Each
   gate's hypotheses must be re-established at the accumulated frame. This is
   the bulk of it and it is pure bookkeeping — `Env.lookup_set_ne` per fact —
   now that `execStmt_of_singleton` exists. `probe_block_runs` is the worked
   example: four gates, four `rw`s, ~15 lines.
2. **The world chain.** `w` → counter bump (statement 1) → cell + closure
   (statement 7) → generator alloc and one step (the loop) → the store
   (statement 15). Four world changes, each already the conclusion of its gate.
3. **`callIn`'s own boundary** — `callIn.eq_2`, `sbCallEnv` (proved) for the
   entry frame, and the `.ret` arm carrying `best` out.
4. **THREE OPEN PREMISES**, all named and none blocking:
   * `hev`/`hyield` — the `moves()` call allocating its generator, and that
     generator's FIRST step yielding `(None, None)` from the `depth == 0`
     clause. The sunfish analogue of §L9's `moves_call_creates`, plus one
     `stepIter` through two statements of `moves()`.
   * `calm`'s genexp (§L18) — `any(<genexpr@3>("RBNQ", pos))`, open by design at
     depth 0 because nothing reads `calm` there.
   Under the recorded model choice (§L18) the futility premise is definitional,
   so it does NOT appear here; the sort-order theorem's tail step (§L17 item (a))
   remains the immediately-next inch after the assembly and does not block it.

**`model_audit` CANNOT RETIRE.** But the ledger is worth stating plainly: at the
start of §L17 the interpreter half was UNSTARTED, and the distance was seven
statements plus the fold plus the tail plus the assembly. It is now the assembly
alone, with a worked example of every piece it composes.
