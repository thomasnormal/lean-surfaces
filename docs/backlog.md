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
mapping, argv a marshalled global. Sequencing: v0 after the H1 stages —
module-level execution of current-tier scripts (loudly refusing
`def`/assignment interleaving until the ordered `ModuleItem`
representation lands), first-unsupported-construct reporting, stdout diff
vs python3.9, harness script-corpus mode; then the ladder continues (H2
lists, H3 classes, H4 generators) with corpus telemetry as the
prioritization signal beside the sunfish milestones; sunfish-under-leanpy
is the capstone once the tier admits it (likely post-H4). A single-call
convenience driver (`tools/lean-python`: extract → `leanmodels-run`, with
an optional one-off CPython comparison) exists today.

## Python tier: the sunfish ladder (steps 3-6)

Steps 1-2 are BUILT (G1 constant globals; `for` over lists/tuples;
builtins `max`/`min`/`abs`/`int`) with proved sunfish acceptance examples
(`Examples/python/sf_consts`, `sf_builtins`, `sf_bound_for`,
`sf_bound_tree`). The remaining steps toward running Lean proofs against
sunfish.py as shipped, in dependency order, each with its blocking design
decision:

3. **Dicts (read tier first).** `Val.dict` as an insertion-ordered
   assoc array (CPython 3.7+ order), dict literals, subscript READ,
   `len`, `in`; unlocks sunfish's `pst`/`piece` tables and the real
   defining expressions of `MATE_LOWER`/`MATE_UPPER`
   (`piece["K"] + 10 * piece["Q"]` — the G1 evaluator's `indexVal`
   handles it once dict values exist). DESIGN DECISION (owner): dict
   WRITES are aliasing-visible mutation — the v0 value semantics cannot
   express them faithfully (same reason `list +=` is refused). Options:
   (a) read-only dicts, all writes loudly `unsupported` (enough for
   pst/eval; the TT stays out); (b) a heap/reference layer — a major
   architectural change that would ripple through every proof rule.
4. **Classes/namedtuple methods.** `Position` is a frozen namedtuple —
   value semantics are FAITHFUL for it; `Searcher` mutates `self` (TT,
   killer) and needs the heap decision from step 3(b). A namedtuple-only
   tier (attribute read + method call on immutable records) would unlock
   `Position.value()` (with step 5) and a self-less `bound()`.
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
