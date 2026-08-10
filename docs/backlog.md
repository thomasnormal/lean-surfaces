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
2. **Instance-receiver method keywords** — `self.bound(…, root=True)`
   (sunfish.py 401/568) wants the kwarg merge on the `execAttrCall`
   path; closure-gated anyway (see 3).
3. **`moves()` is a nested def** (the standing capstone gap): closures
   over `pos`/`gamma`/`depth`/`root`/`self`, plus `Searcher.bound`
   itself. The ordering surface now waits ONLY on this.
4. **The module-init padding loop** (`pst.items()` + lambda + `sum`
   over a genexp): would let the SHIPPED file's `value()` resolve `pst`
   instead of the oracle-generated table in `sf_order`.
5. **The ordering theorem** — extend the decided reference-enumeration
   equality from `gen_moves` to the ordered `(value, move)` list
   (`sf_order.order_from` is its concrete anchor).
