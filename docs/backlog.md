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
   `sf_bound_rec`, `bench_bisect`, `bench_statistics`) — the intended
   rescue route is an `execForList` ≡ `execFor`-on-snapshot equivalence
   lemma over pinned worlds, so the frozen-tail `for` induction pattern
   survives; then the arg-mutation harness rows go live and `+= `/list
   concat can revisit the heap-free-fragment question.

4. **Classes — BUILT (H3, 2026-08-08),** per docs/memory-model.md
   §class semantics: ClassDef end to end (the three sunfish ClassDef
   bodies represented), methods flattened to qualified-name functions
   through `callIn`/`CallsIn` (no new call judgment), `Obj.instance`
   with mutable self, faithful `AttributeError`, the dunder guard making
   default-object semantics sound, `Searcher`'s tables proved
   (`Examples/python/sf_searcher`: the cross-call write/read pair).
   REMAINING from this step — **namedtuple, DECIDED value-like**
   (immutable = immediate; field access desugars to tuple indexing —
   which keeps sunfish's `tp_score` keys in the pure `keyEq` tier;
   recorded in memory-model §class semantics): a value-record tier for
   `Position`/`Entry`/`Move` — recognize `X = namedtuple(…)` at G1,
   constructor calls, field reads, methods on an immutable self
   (`class Position(namedtuple(…))` carries methods; its base today
   keeps it loudly uninstantiable). Would unlock `Position.value()`
   (with step 5) and `bound()` over real positions.
5. **String methods + slicing.** `board[:i] + p + board[i+1:]` (move
   application), `.isupper()`, `.swapcase()`, `.index()`. Value
   semantics faithful (str immutable); mostly interpreter surface.
6. **Generators (hardest) + `sorted(key=)`.** `moves()` interleaves
   search effects with iteration and `bound` consumes it lazily —
   the beta cutoff means eager pre-expansion diverges on real trees.
   DESIGN DECISION (owner): semantics as (a) CPS/step-indexed iterator
   values in `Val`, (b) a desugaring for the restricted
   generator-consumed-by-one-for-loop shape sunfish uses, or (c) keep
   generators out and certify a generator-free `sunfish_core.py` that
   sunfish imports (the transliteration then ships as the engine).

Cross-cutting, found by the milestone proofs: `py_vcgen` cannot walk
`for` loops (the frozen-`execFor` list-induction pattern in
`Examples/python/sf_bound_for/proof.lean` is the manual route to
automate); the two while-loop walker gaps reproduced in
`Examples/python/sf_bound_loop/proof.lean.blocked-by-py_vcgen-gaps`
(builtin lookup stuck behind the symbolic env tail; symbolic-subscript
range guards needing arithmetic discharge); `arrVal_getElem`-family
lemmas still example-local (F-6); (the former int-only CLI gap is CLOSED:
`leanmodels-run` accepts canonical typed JSON arguments and the sf list
and tree functions carry differential rows).
