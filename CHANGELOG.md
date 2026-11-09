# Changelog

## Unreleased

- Extended the value/object evaluator agreement battery with compound
  bitwise-OR assignment and native differential coverage.

- Extended the value/object evaluator agreement battery with compound
  bitwise-AND assignment and native differential coverage.

- Extended the value/object evaluator agreement battery with compound modulo
  assignment and native differential coverage.

- Extended the value/object evaluator agreement battery with compound
  division assignment and native differential coverage.

- Extended the value/object evaluator agreement battery with compound
  multiplication assignment and native differential coverage.

- Extended the value/object evaluator agreement battery with compound
  subtraction assignment and native differential coverage.

- Extended the value/object evaluator agreement battery with a greater-than-
  or-equal comparison callable and native differential row.

- Extended the value/object evaluator agreement battery with a less-than-or-
  equal comparison callable and native differential row.

- Extended the value/object evaluator agreement battery with a greater-than
  comparison callable and native differential row.

- Extended the value/object evaluator agreement battery with an inequality
  comparison callable and native differential row.

- Extended the value/object evaluator agreement battery with an equality
  comparison callable and native differential row.

- Extended the value/object evaluator agreement battery with a less-than
  comparison callable and native differential row.

- Extended the value/object evaluator agreement battery with a right-shift
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a left-shift
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a bitwise-XOR
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a bitwise-OR
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a bitwise-AND
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a safe modulo
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a safe integer
  division callable and native differential row.

- Extended the value/object evaluator agreement battery with a binary
  subtraction callable and native differential row.

- Extended the value/object evaluator agreement battery with a binary
  multiplication callable and native differential row.

- Corrected the C++ differential harness to classify native assertion failures
  as `DIVERGE`, print the pinned Clang version, and require an available oracle
  by default in CI.

- Extended the value/object evaluator agreement battery with a logical-not
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a bitwise-not
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a unary-plus
  callable and native differential row.

- Extended the value/object evaluator agreement battery with the true-path
  short-circuit logical-AND callable and native differential row.

- Extended the value/object evaluator agreement battery with a short-circuit
  logical-OR callable and native differential row.

- Restored the value/object evaluator agreement battery's direct parameter
  return callable and native differential row.

- Extended the value/object evaluator agreement battery with an explicit
  integral-conversion callable and native differential row.

- Extended the value/object evaluator agreement battery with a `noexcept`
  callable and native differential row.

- Extended the value/object evaluator agreement battery with an integer-literal
  callable and native differential row.

- Extended the value/object evaluator agreement battery with an `alignof`
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a `sizeof`
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a null-pointer
  comparison callable and native differential row.

- Extended the value/object evaluator agreement battery with a parameter
  assignment callable and native differential row.

- Extended the value/object evaluator agreement battery with a label and
  `goto` callable and native differential row.

- Extended the value/object evaluator agreement battery with a loop `continue`
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a loop `break`
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a statement-level
  conditional callable and native differential row.

- Extended the value/object evaluator agreement battery with a comma
  expression callable and native differential row.

- Extended the value/object evaluator agreement battery with a decrementing
  `for` callable and native differential row.

- Extended the value/object evaluator agreement battery with a `do-while`
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a direct
  `switch` callable and native differential row.

- Extended the value/object evaluator agreement battery with an initially-false
  `while` callable and native differential row.

- Extended the value/object evaluator agreement battery with a conditional
  expression callable and native differential row.

- Extended the value/object evaluator agreement battery with a unary arithmetic
  callable and native differential row.

- Extended the value/object evaluator agreement battery with a compound
  assignment callable and native differential row.

- Extended the value/object evaluator agreement battery with a binary
  arithmetic callable and native differential row.

- Named the object evaluator's direct-call refusal `unsupportedCall` and added
  a differential refusal witness with a dedicated harness renderer.

- Centralized integral type extraction in `ScalarArithmetic` for both callable
  evaluators and added a builtin/qualified/non-integral witness.

- Centralized profile format selection in `ScalarArithmetic` for both callable
  evaluators and added a qualified/unsupported evidence witness.

- Centralized evidence-to-value conversion in `ScalarArithmetic` for both
  callable evaluators and added a builtin/qualified/unsupported witness.

- Centralized null-pointer comparison decoding in `ScalarArithmetic` for both
  callable evaluators and added an agreement witness.

- Centralized promoted increment/decrement arithmetic in `ScalarArithmetic`
  for both callable evaluators and added success, qualified, and Boolean
  controls.

- Centralized typed `alignof` value construction in `ScalarArithmetic` for both
  callable evaluators and added an agreement witness.

- Centralized typed `sizeof` value construction in `ScalarArithmetic` for both
  callable evaluators and added an agreement witness.

- Centralized typed integer-literal construction in `ScalarArithmetic` for
  both callable evaluators and added an agreement witness.

- Centralized `++`/`--` increment operator spelling decoding in
  `ScalarArithmetic` for both callable evaluators and added an agreement
  witness.

- Centralized switch case/default suffix selection in `Callable` for both
  callable evaluators and added a matching/default agreement witness.

- Centralized `IntegralResult` map and bind propagation in `ScalarArithmetic`
  for both callable evaluators and added a success/undefined witness.

- Centralized compound-assignment operator spelling decoding in
  `ScalarArithmetic` for both callable evaluators and added an agreement
  witness.

- Centralized unary and binary operator spelling decoding in `ScalarArithmetic`
  for both callable evaluators and added an agreement witness.

- Python: rebase the legacy `ClockErase` proof over the five-field world and
  current generator, set, call-depth, and structured-statement semantics.

- Docs: update the import-admission and trace-clock sections to describe the
  structured AST whitelist instead of the retired text-keyed path.

- Docs: clarify that the monadic refinement edge currently covers the shared
  pure workers, while control and script adequacy remain explicit debt.

- Docs: record the remaining namedtuple static-table boundary and its
  source-order guard; runtime namedtuple construction remains future work.

- Docs: record the guarded module-level callable-alias slice and its remaining
  first-class-function representation debt.

- Docs: record that trailing definition deletes remain source nodes and loud
  until runtime definition bindings are implemented.

- Docs: record that `yield from` remains a structured loud boundary rather than
  an extractor-generated `for` loop.

- Docs: clarify the structured class statement boundary and qualified method
  dispatch index, including creation-purity admission.

- Docs: record that extractor `Try`/`Raise` nodes retain structured clauses;
  shape-specific handler and finalizer lowerings remain absent.

- Docs: record the structured display/comprehension boundaries and the limited
  measured starred-target/call slices.

- Docs: catalog the remaining explicit ingestion compatibility bridges and
  their loud or guarded interpreter cases.

- Docs: record the pinned leanpy frontend/oracle behavior and visible fallback
  warnings.

- Docs: record frontend metadata admission and envelope freshness as enforced
  gates.

- Docs: record the expanded differential edge battery covering audited refusal
  and recursion/set/comprehension boundaries.

- Docs: record the parameterized float-round worker and its cutoff boundary
  battery.

- CI: confirm superseded workflow runs are cancelled per ref and both long jobs
  have bounded timeouts.

- Docs: recheck the CPython 3.9 recursion-limit model, including active-depth
  restoration across returns, raises, and sibling calls.

- Python: rebase the `float_lab` proof's symbolic execution over the active
  call-depth guard and structured import resolution; the real float example
  proof and spec build cleanly under Lean 4.35.

- Tests: recheck the audited Python edge-row coverage against the pinned
  CPython 3.9 script corpus; all 158 scripts remain either matched or an
  explicit loud boundary.

- Python: recheck the parameterized float-round worker and its CPython cutoff
  boundary battery; no per-digit worker family remains.

- Docs: record the next measured completeness milestone: a native `ListComp`
  evaluator over the existing heap-list and iterator workers, with the
  source-level comprehension shadow boundary retained until that seam lands.

- Docs: pin the ListComp recursion design: per-element evaluation must enter
  the explicit `Kont` fuel boundary rather than recurse through a fuel-free
  `evalOpen` helper.
- Centralized logical `&&`/`||` decoding and short-circuit decisions in
  `ScalarArithmetic` for both callable evaluators and added a value/object
  agreement witness.

- Python: recheck the Lean 4.35 fixture and exception-proof repairs after the
  master bump; the five-field world literals and handler normalization are
  already present on current master.

- Added the remaining measured dictionary-source set witnesses to the loud
  differential whitelist, including the length-only `set(d.keys())` path.

- Python: enforce the pinned CPython 3.9 recursion limit on closed-function
  calls, restoring the active frame depth after returns and raises so sibling
  calls do not consume one another's stack budget.

- Repaired the closed-call proof geometry after adding frame depth: public
  `callFunction` now starts at the ordinary zero-depth world, matching the
  stateful `CallsIn` frame and keeping the recursion guard in the body.

- Updated the remaining Python proof fixtures and generator guard for the
  five-field `World` record introduced by the recursion-limit model.

- Rebased the exception-ancestor proof's handler normalization onto the
  structured primary and bare-handler predicates.

- Pinned stale example checks to the exact loud refusals produced after the
  removed lowering paths, retaining each former CPython answer as a comment.

- Retired the false finite-float set-consumer theorem after set displays became
  a loud boundary; finite dictionary and tuple-key theorems remain intact.

- Rechecked the position-independent module definition boundary: forward
  function-body calls and duplicate module definitions remain loud rather than
  answering through the static table.

- Rechecked structured `global` and `nonlocal` declarations: names come from
  the approved AST arrays, with no source-text reparsing or 200-character
  truncation path.

- Rechecked generator-expression capture and creation-time iteration guards:
  unsafe rebinding remains loud, and non-iterable outer sources raise before
  the first resume.

- Rechecked the generator-expression creation-time `GET_ITER` guard: scalar
  outer sources raise at creation rather than answering after deferred resume.

- Rechecked list-comprehension shadowing: the approved AST preserves
  `ListComp` as a structured loud boundary, so user bindings cannot affect it.

- Rechecked augmented-repeat semantics: the retired shape-specific rewrite is
  absent, so in-place list mutation and `*=` error behavior remain faithful.

- Rechecked expression-yield target handling: global and nonlocal dead-yield
  stores remain explicit loud boundaries instead of dropping the resumed store.

- Rechecked non-simple annotated-assignment ordering: values and stores happen
  before module/class annotation evaluation, while function annotations stay
  unevaluated.

- Rechecked length-only repetition removal: `len(sequence * count)` follows
  ordinary materialization, with oversized products remaining loud instead of
  returning a fabricated length.

- Refused set construction from dictionary sources: CPython's pre-sized
  merge table gives iteration order the model cannot reproduce, so both small
  and wide `set(dict)` witnesses now fail loudly.

- Rechecked removal of exact two-statement ingestion rewrites: source pairs
  remain structured and reach the existing loud semantic boundaries.

- Rechecked static definition deletion: function-body references no longer
  admit a deleted `def`/`class`/namedtuple as a no-op; definition deletes stay
  loud until runtime bindings exist.

- Rechecked trace-clock readings: zero-argument `time.time()` remains loud
  while the explicit integer trace awaits a binary64 representation; argument
  arity and dead-clock rows retain their measured behavior.

- Removed the extractor's last supported semantic `ast.unparse` lookup:
  benign `from itertools/collections` admission now keys directly on AST
  module and alias fields, leaving unparsed text diagnostic-only.

- Rechecked the monadic-to-trunk refinement boundary: the kernel-checked
  `twinAgrees_liftRes` and `twinAgrees_binOp` edges remain landed, with the
  mutually recursive control adequacy theorem still explicit debt.

- Rechecked namedtuple recognition: source-order and import-order guards keep
  unsafe static-table candidates loud, while the admitted value-like namedtuple
  battery remains unchanged.

- Rechecked module-level callable aliases: static dispatch stays source-order
  guarded, later live shadows remain dynamic, and identity/forward hazards stay
  loud until first-class function objects replace the copied table entries.

- Rechecked trailing definition deletion: ingestion preserves every `del`
  statement and the script surface refuses static `def`/`class`/namedtuple
  tombstones instead of rewriting them to `pass`.

- Rechecked `yield from`: the extractor and ingestion preserve a structured
  delegation node, and resumed delegation remains loud until a PEP 380 frame
  models send, throw, close, and the delegation return value.

- Rechecked structured class statements: class creation purity is decided at
  the statement boundary, while qualified method indexing remains the
  intentional dispatch representation and effectful creation stays loud.

- Rechecked extractor `try` handling: handler, `else`, `finally`, generator,
  and raise nodes stay structured with explicit loud reasons; no nested-try,
  reordered-finalizer, synthetic-flag, or `raise N()` rewrite remains.

- Rechecked display/comprehension/starred extraction boundaries: unsupported
  displays remain explicit source nodes, while the landed list-comprehension,
  positional-star, and flat-star-target slices retain their loud or guarded
  behavior without shadowable builtin names.

- Rechecked the remaining general ingestion bridges: retired source-shape
  rewrites stay absent, while f-string, multi-item `with`, delete-target,
  chained-assignment, dictionary-view, and type-error-handler markers remain
  explicit documented debt or loud boundaries.

- Rechecked leanpy pinning: extraction re-execs under CPython 3.9, comparison
  defaults to the pinned 3.9 oracle, and survey fallback warnings remain
  covered by the runner tests.

- Rechecked frontend admission and envelope freshness: Python ingestion rejects
  foreign frontend families, and the committed corpus is fresh under CPython
  3.9 with the gate's refusal/self-test paths intact.

- Rechecked differential edge coverage: the pinned 4,202-case battery now
  carries negative-hash, dict-source, copy/intersection, generator-creation,
  recursion, scoping, annotation, and oversized-materialization witnesses with
  zero failures.

- Rechecked the parameterized float-round worker: the per-digit family remains
  retired, with one `roundFloatNDigits` dispatch and boundary tests covering
  large and negative `ndigits` values.

- Added a kernel-checked `PyLe.foldlM` congruence and wired it into the monadic proof walkers for stateful list folds.

- Preserved list comprehensions as structured `ListComp` nodes through extraction and ingestion; evaluation remains a loud explicit boundary instead of a shadowable `list` call, with proof walkers and differential witnesses updated.

- Closed the stale JSON list-comprehension lowering path; `ListComp` remains an explicit loud boundary and no longer becomes a shadowable `list` call.

- Repaired payload-blind proofs for zero-argument user and admitted builtin exception constructors; runtime behavior is unchanged.

- Refreshed the generated Python coverage page after the current differential battery moved from one divergence to zero.

- Refreshed the two stale Python lab envelopes found by the pinned frontend freshness gate; the committed envelope set is fresh again.

- Namedtuple table recognition now requires the structured benign import to
  precede every candidate. A candidate written before
  `from collections import namedtuple` stays on the loud runtime path, so
  ingestion cannot move the import before its CPython execution point.

- Script mode now poisons copied function aliases that have a later ordinary
  binding, so function bodies consult the live module frame instead of calling
  a stale static alias entry; the scalar shadow now reproduces CPython's
  `TypeError`. General function-object values remain outside the tier.

- Rechecked trailing module definition deletion: the `del` statement remains
  in the AST and reaches the loud static-table boundary. Removed stale
  comments that still described an ingestion rewrite to `pass`.

- Rechecked `yield from`: ingestion now retains the structured delegation node
  and has no synthetic loop target. Resumed delegation remains loud until a
  PEP 380 frame models send, throw, close, and the delegation return value.

- Rechecked class ingestion: source-order `.classDef` markers and retained
  class bodies preserve creation effects, while qualified method indexing
  remains the deliberate dispatch representation. Unsupported creation stays
  loud until runtime class namespaces and class objects are modeled.

- Retained structured `Try` and `Raise` nodes through extraction. Removed the
  dead try-else marker and stale shape-lowering descriptions; `raise N()` now
  reaches the interpreter as a call expression, while unsupported cleanup and
  handler forms remain loud.

- Removed the unused starred-display lowering and its shadow census. Starred
  displays and set/list/dict comprehensions remain explicit loud AST boundaries;
  landed starred assignment, loop-target, and positional-call slices stay
  separate.

- Rechecked general ingestion translations: retired comprehension, starred-display,
  and raise-cause rewrites remain absent; the remaining dict-view, deletion,
  with-item, chain, and f-string bridges stay documented as measured debt.

- Clarified that global declarations stay structured from the CPython AST through scope setup; the stale source-text comment is gone.

- Repaired tuple and string repetition proof recipes after removing the
  length-only ingestion rewrite; `len(sequence * count)` now follows ordinary
  materialization and keeps oversized results loud.

- Corrected the set iteration example and documentation to match the bounded
  nonnegative integer hash subset; negative integer iteration remains loud.

- Synchronized generator-capture documentation with the removal of
  shape-specific ingestion rewrites; named generator assignments now remain
  in the AST and body captures use shared cells.

- Clarified that module definition deletions, including trailing deletes, stay
  loud until definitions become runtime bindings; only unobserved benign-import
  deletion retains its narrow no-op path.

- Kept CPython's clock oracle values as binary64 floats in differential replay;
  the model's integer trace remains an explicit loud boundary until binary64
  trace readings are modeled.

- Rechecked the structured-AST text boundary: supported semantics no longer
  parses diagnostic text from unsupported nodes or reconstructed import and
  handler payloads.

- Clarified the two-interpreter status: pure-worker refinement theorems are
  landed, while the mutually recursive control and script adequacy edge remains
  outstanding.

- Verified the ordered module-definition admission against the forward-reach and redefinition fixtures; the script corpus keeps both hazards loud while the structured long-global row matches CPython.

- Kept `nonlocal` loud in the proof interpreter instead of returning a stale cell value; the monadic runner remains the executable cell implementation.

- Completed the payload-blind proof walker for structured `import` and class-definition statement nodes; the umbrella Lean artifact now builds through the Python proof layer.

- Refreshed the set-lab envelope and generated Python coverage page after the audit-row and explicit refusal updates.

- Rebased the round-lab proof artifact on the parameterized float-round worker; all 53 round theorems build without deleted per-digit helper references.

- Refreshed the generated backlog index after cross-lane entries landed, restoring documentation freshness.

- Restored fail-closed refusal-census taxonomy coverage for all unsupported differential rows and loud script witnesses; unclassified inventory entries now fail the gate.

- Added an end-to-end pinned differential test for float `round` values beyond the former per-digit worker range and at both exponent cutoffs.

- Added differential witnesses for negative and constructed set iteration paths; synchronized script expectations with the intentional loud boundaries for displays and definition deletion.

- CI now cancels superseded runs per ref and bounds the full check with a 180-minute job timeout.

- Python envelope freshness is now a required full-CI and `--python-only` gate; leanpy regression coverage verifies foreign frontend stamps are rejected before execution.

- Added CI-wired regression coverage for leanpy's CPython 3.9 frontend/oracle pinning and the survey's explicit fallback warning.

- `raise X from cause` now retains its structured cause through ingestion; cause-bearing raises remain loud until exception chaining is modeled.

- Removed builtin-name and synthetic-temporary lowerings for set/list/dict comprehensions, starred displays, starred calls, and starred loop targets; these AST shapes now refuse through explicit boundaries.

- Removed shape-specific `try`/`finally`/`else` and generator-handler extractor lowerings; structured `Try` nodes now retain loud reasons for unsupported cleanup and generator-frame semantics.

- Class definitions now retain a structured `.classDef` statement marker through ingestion and execution; qualified method indexing remains available while unsupported class execution stays loud.

- Statement-position `yield from` now remains a structured `YieldFrom:delegation` refusal instead of being inlined into a synthetic `for` loop; helper-driven generator rows retain their admitted behavior.

- Trailing `del` statements targeting static definitions are preserved in the AST and refuse at script execution instead of being rewritten to `pass`.

- Added a differential witness for callable-alias identity; `alias is target` now remains an explicit loud boundary while admitted alias calls keep their existing tier.

- Namedtuple table resolution now requires the definition to precede every function body that reaches it; unsafe forward reachability refuses instead of using a position-independent static table.

- Added the first `twinAgrees` refinement lemmas: monadic pure-worker lifts and binary operators are proved equal to the theorem interpreter's `Run.liftRes` path.

- Removed the unused exception-handler name delimiter encoder; handler semantics now retain structured name arrays end to end.

- Plain `import time` is now a structured AST statement; import admission and the clock census no longer parse source-text whitelist strings, while richer imports remain loud.

- Float `round(number, ndigits)` now uses one exact-ratio worker with CPython's positive and negative exponent cutoffs; the former per-digit workers and proof branches were removed.

- Refuse zero-argument `time.time()` reads while the trace carries only
  integers; CPython returns binary64 floats. Positional arity errors remain
  faithful and do not consume the trace.

- First-class callable aliases now refuse after argument evaluation instead
  of fabricating a not-callable `TypeError` after the shape-specific alias
  rewrites were removed.

- Float `round(number, 30)` now uses an exact binary64 ratio scaled by one nonillion, preserving ties-to-even and signed zero.

- Float `round(number, 31)` now uses an exact binary64 ratio scaled by ten nonillion, preserving ties-to-even and signed zero.

- Float `round(number, 32)` now uses an exact binary64 ratio scaled by one hundred nonillion, preserving ties-to-even and signed zero.

- Float `round(number, 33)` now uses an exact binary64 ratio scaled by one decillion, preserving ties-to-even and signed zero.

- Float `round(number, 34)` now uses an exact binary64 ratio scaled by ten decillion, preserving ties-to-even and signed zero.

- Float `round(number, 35)` now uses an exact binary64 ratio scaled by one hundred decillion, preserving ties-to-even and signed zero.

- Float `round(number, 36)` now uses an exact binary64 ratio scaled by one undecillion, preserving ties-to-even and signed zero.

- Float `round(number, 37)` now uses an exact binary64 ratio scaled by ten undecillion, preserving ties-to-even and signed zero.

- Float `round(number, 38)` now uses an exact binary64 ratio scaled by one hundred undecillion, preserving ties-to-even and signed zero.

- Float `round(number, 39)` now uses an exact binary64 ratio scaled by one duodecillion, preserving ties-to-even and signed zero.

- Float `round(number, 40)` now uses an exact binary64 ratio scaled by ten duodecillion, preserving ties-to-even and signed zero.

- Float `round(number, 41)` now uses an exact binary64 ratio scaled by one hundred duodecillion, preserving ties-to-even and signed zero.

- Float `round(number, 42)` now uses an exact binary64 ratio scaled by one tredecillion, preserving ties-to-even and signed zero.

- Float `round(number, 43)` now uses an exact binary64 ratio scaled by ten tredecillion, preserving ties-to-even and signed zero.


- Float `round(number, 29)` now uses an exact binary64 ratio scaled by one hundred octillion, preserving ties-to-even and signed zero.


- Float `round(number, 28)` now uses an exact binary64 ratio scaled by ten octillion, preserving ties-to-even and signed zero.


- Float `round(number, 27)` now uses an exact binary64 ratio scaled by one octillion, preserving ties-to-even and signed zero.


- Float `round(number, 26)` now uses an exact binary64 ratio scaled by one hundred septillion, preserving ties-to-even and signed zero.


- Float `round(number, 25)` now uses an exact binary64 ratio scaled by ten septillion, preserving ties-to-even and signed zero.


- Float `round(number, 24)` now uses an exact binary64 ratio scaled by one septillion, preserving ties-to-even and signed zero.


- Float `round(number, 23)` now uses an exact binary64 ratio scaled by one hundred sextillion, preserving ties-to-even and signed zero.


- Refreshed the `tri` proof's symbolic simplification for the late exception-name census, restoring the Python quickstart proof on current semantics.


- Float `round(number, 22)` now uses an exact binary64 ratio scaled by ten sextillion, preserving ties-to-even and signed zero.


- Float `round(number, 21)` now uses an exact binary64 ratio scaled by one sextillion, preserving ties-to-even and signed zero.


- Float `round(number, 20)` now uses an exact binary64 ratio scaled by one hundred quintillion, preserving ties-to-even and signed zero.


- Float `round(number, 19)` now uses an exact binary64 ratio scaled by ten quintillion, preserving ties-to-even and signed zero.


- Float `round(number, 18)` now uses an exact binary64 ratio scaled by one quintillion, preserving ties-to-even and signed zero.


- Float `round(number, 17)` now uses an exact binary64 ratio scaled by one hundred quadrillion, preserving ties-to-even and signed zero.


- Float `round(number, 16)` now uses an exact binary64 ratio scaled by ten quadrillion, preserving ties-to-even and signed zero.


- Float `round(number, 15)` now uses an exact binary64 ratio scaled by one quadrillion, preserving ties-to-even and signed zero.


- Float `round(number, 14)` now uses an exact binary64 ratio scaled by one hundred trillion, preserving ties-to-even and signed zero.


- Float `round(number, 13)` now uses an exact binary64 ratio scaled by ten trillion, preserving ties-to-even and signed zero.


- Float `round(number, 12)` now uses an exact binary64 ratio scaled by one trillion, preserving ties-to-even and signed zero.


- Float `round(number, 11)` now uses an exact binary64 ratio scaled by one hundred billion, preserving ties-to-even and signed zero.


- Float `round(number, 10)` now uses an exact binary64 ratio scaled by ten
  billion, preserving ties-to-even and signed zero. Larger positive digit
  counts and other digit protocols remain loud.

- Float `round(number, 9)` now uses an exact binary64 ratio scaled by one
  billion, preserving ties-to-even and signed zero. Larger positive digit
  counts and other digit protocols remain loud.

- Float `round(number, 8)` now uses an exact binary64 ratio scaled by one
  hundred million, preserving ties-to-even and signed zero. Larger positive
  digit counts and other digit protocols remain loud.

- Float `round(number, 7)` now uses an exact binary64 ratio scaled by ten
  million, preserving ties-to-even and signed zero. Larger positive digit
  counts and other digit protocols remain loud.

- Float `round(number, 6)` now uses an exact binary64 ratio scaled by one
  million, preserving ties-to-even and signed zero. Larger positive digit
  counts and other digit protocols remain loud.

- Float `round(number, 5)` now uses an exact binary64 ratio scaled by one
  hundred thousand, preserving ties-to-even and signed zero. Larger positive
  digit counts and other digit protocols remain loud.

- The `round(number, ndigits)` slice now admits integral `ndigits == 0`,
  preserving CPython's integer/bool result types and exact binary64 float
  ties-to-even behavior. Other `ndigits` values remain loud; the focused
  example and differential battery cover the admitted forms.

- Integral and Boolean `round(number, ndigits)` calls now preserve their
  integer result for nonnegative integral `ndigits`. Float calls remain
  limited to the exact `ndigits == 0` slice; negative and richer digit
  protocols remain loud.

- Float `round(number, 1)` now uses an exact binary64 ratio scaled by ten,
  including signed-zero behavior. Larger positive digit counts and other
  digit protocols remain loud.

- Float `round(number, 2)` now uses an exact binary64 ratio scaled by one
  hundred, preserving ties-to-even and signed zero. Larger positive digit
  counts remain loud.

- Float `round(number, 3)` now uses an exact binary64 ratio scaled by one
  thousand, preserving ties-to-even and signed zero. Larger positive digit
  counts remain loud.

- Float `round(number, 4)` now uses an exact binary64 ratio scaled by ten
  thousand, preserving ties-to-even and signed zero. Larger positive digit
  counts remain loud.

- One-argument `round(float)` now uses the exact binary64 ratio with
  ties-to-even rounding, including CPython's `ValueError` for NaN and
  `OverflowError` for infinity. The `ndigits` form remains loud. A focused
  proof example and 12-row native/proof differential battery cover the new
  behavior.

- Synchronized the closure proof regression with the proof interpreter's
  target-specific cell guard: `gen_cell_after_call` now checks
  `proofCallFunction`, so the example cannot accept the stale snapshot result
  from the legacy value interpreter.

- Repaired the Python proof layer after dynamic exception-handler shadowing
  changed the interpreter guard: `PayloadBlind` now follows the semantics
  guard, and the VC tests expose the new helper reductions. `lake build
  LeanModels` passes on a clean managed build.

- C++ callable-frame coverage now includes a negative-false while-inside-
  `switch` shadow fallthrough assignment `continue` witness, with a native
  differential match and 1,530 total rows.

- C++ callable-frame coverage now includes a negative-false while-inside-
  `switch` shadow fallthrough assignment `return` witness, with a native
  differential match and 1,529 total rows.

- C++ callable-frame coverage now includes a negative-false while-inside-
  `switch` shadow fallthrough assignment false-path witness, with a native
  differential match and 1,528 total rows.

- C++ callable-frame coverage now includes a negative-false while-inside-
  `switch` shadow assignment false-path witness, with a native differential
  match and 1,527 total rows.

- C++ callable-frame coverage now includes a negative-false while-inside-
  `switch` shadow assignment `break` witness, with a native differential
  match and 1,526 total rows.

- C++ callable-frame coverage now includes a negative-false while-inside-
  `switch` shadow assignment `return` witness, with a native differential
  match and 1,525 total rows.

- C++ callable-frame coverage now includes a negative-false while-inside-
  `switch` shadow assignment `continue` witness, with a native differential
  match and 1,524 total rows.

- C++ callable-frame coverage now includes a negative-false default-case
  `for`-inside-`switch` shadow assignment `break` witness, with a native
  differential match and 1,523 total rows.

- C++ callable-frame coverage now includes a negative-false default-case
  `for`-inside-`switch` shadow assignment `continue` witness, with a native
  differential match and 1,522 total rows.

- C++ callable-frame coverage now includes a negative-false default-case
  `for`-inside-`switch` shadow assignment false-path witness, with a native
  differential match and 1,521 total rows.

- C++ callable-frame coverage now includes a negative-false default-case
  `for`-inside-`switch` shadow assignment `return` witness, with a native
  differential match and 1,520 total rows.

- C++ callable-frame coverage now includes a negative-false default-case
  `for`-inside-`switch` shadow fallthrough assignment `break` witness, with
  a native differential match and 1,519 total rows.

- C++ callable-frame coverage now includes a negative-false default-case
  `for`-inside-`switch` shadow fallthrough assignment `continue` witness,
  with a native differential match and 1,518 total rows.

- C++ callable-frame coverage now includes a negative-false default-case
  `for`-inside-`switch` shadow fallthrough assignment `return` witness, with
  a native differential match and 1,517 total rows.

- C++ callable-frame coverage now includes a negative-false default-case
  `for`-inside-`switch` shadow fallthrough assignment witness, with a native
  differential match and 1,516 total rows.

- C++ callable-frame coverage now includes a negative-false `for`-inside-
  `switch` shadow fallthrough assignment `break` witness, with a native
  differential match and 1,515 total rows.

- C++ callable-frame coverage now includes a negative-false `for`-inside-
  `switch` shadow fallthrough assignment `continue` witness, with a native
  differential match and 1,514 total rows.

- C++ callable-frame coverage now includes a negative-false `for`-inside-
  `switch` shadow fallthrough assignment `return` witness, with a native
  differential match and 1,513 total rows.

- C++ callable-frame coverage now includes a negative-false `for`-inside-
  `switch` shadow fallthrough assignment witness, with a native differential
  match and 1,512 total rows.

- C++ callable-frame coverage now includes a negative-false `for`-inside-
  `switch` shadow assignment false-path witness, with a native differential
  match and 1,511 total rows.

- C++ callable-frame coverage now includes a negative-false `for`-inside-
  `switch` shadow assignment `return` witness, with a native differential
  match and 1,510 total rows.

- C++ callable-frame coverage now includes a negative-false `for`-inside-
  `switch` shadow assignment `break` witness, with a native differential
  match and 1,509 total rows.

- C++ callable-frame coverage now includes a negative-false `for`-inside-
  `switch` shadow assignment `continue` witness, with a native differential
  match and 1,508 total rows.

- C++ callable-frame coverage now includes a negative-false switch shadow
  fallthrough assignment `return` witness, with a native differential match
  and 1,507 total rows.

- C++ callable-frame coverage now includes a negative-false do-while shadow
  initialization assignment `return` witness, with a native differential
  match and 1,506 total rows.

- C++ callable-frame coverage now includes a negative-false do-while shadow
  initialization assignment `break` witness, with a native differential match
  and 1,505 total rows.

- C++ callable-frame coverage now includes a negative-false do-while shadow
  initialization assignment `continue` witness, with a native differential
  match and 1,504 total rows.

- C++ callable-frame coverage now includes a negative-false do-while shadow
  initialization assignment witness, with a native differential match and
  1,503 total rows.

- C++ callable-frame coverage now includes negative-false `for` shadow
  computed initialization assignment `return`, with a native differential
  match and 1,502 total rows.

- C++ callable-frame coverage now includes negative-false `for` shadow
  computed initialization assignment `break`, with a native differential
  match and 1,501 total rows.

- C++ callable-frame coverage now includes negative-false `for` shadow
  computed initialization assignment `continue`, with a native differential
  match and 1,500 total rows.

- C++ callable-frame coverage now includes negative-false `for` shadow
  computed single-assignment initialization, with a native differential match
  and 1,499 total rows.

- C++ callable-frame coverage now includes negative-false `for` shadow
  computed initialization assignment, with a native differential match and
  1,498 total rows.

- The monadic runner now refreshes late-bound cells when an escaped nested
  closure is invoked internally; returning the callable remains loud, and the
  proof interpreter keeps an explicit refusal for this stateful shape.

- The monadic runner now admits generator closures whose enclosing cell is
  rebound between resumes; the proof interpreter keeps its explicit loud
  guard for this stateful shape.

- C++ callable-frame coverage now includes negative-false `for` shadow
  computed initialization `break`, with a native differential match and
  1,496 total rows.

- C++ callable-frame coverage now includes negative-false `for` shadow
  computed initialization `continue`, with a native differential match and
  1,495 total rows.

- C++ callable-frame coverage now includes negative-false `for` shadow
  computed initialization, with a native differential match and 1,494 total
  rows.

- C++ callable-frame coverage now includes negative-false `for` shadow
  initialization assignment `continue`, with a native differential match and
  1,493 total rows.

- C++ callable-frame coverage now includes negative-false `for` shadow
  initialization assignment `return`, with a native differential match and
  1,492 total rows.

- The Pass 0 absent-module import slice now covers unguarded function-body
  `from` imports, preserving CPython's `ModuleNotFoundError` before binding.

- Corrected the trace-clock documentation: one-shot script runs accept
  `--clock i,j,k`, and script-batch jobs accept an optional `"clock"` array.

- C++ callable-frame coverage now includes negative-false `for` shadow
  initialization assignment `break`, with a native differential match and
  1,491 total rows.

- C++ callable-frame coverage now includes negative-false `for` shadow
  initialization assignment, with a native differential match and 1,490 total
  rows.

- C++ callable-frame coverage now includes negative-false `for` shadow
  initialization, with a native differential match and 1,489 total rows.

- C++ callable-frame coverage now includes negative-false do-while local
  initialization `return`, with a native differential match and 1,488 total
  rows.

- C++ callable-frame coverage now includes negative-false do-while local
  initialization `break`, with a native differential match and 1,487 total
  rows.

- C++ callable-frame coverage now includes negative-false do-while local
  initialization `continue`, with a native differential match and 1,486 total
  rows.

- C++ callable-frame coverage now includes negative-false `for` empty-body
  initialization, with a native differential match and 1,485 total rows.

- C++ callable-frame coverage now includes negative-false `for` local
  initialization `return`, with a native differential match and 1,484 total
  rows.

- C++ callable-frame coverage now includes negative-false `for` local
  initialization `break`, with a native differential match and 1,483 total
  rows.

- C++ callable-frame coverage now includes negative-false `for` local
  initialization `continue`, with a native differential match and 1,482 total
  rows.

- C++ callable-frame coverage now includes negative-false `for` zero
  initialization, with a native differential match and 1,481 total rows.

- C++ callable-frame coverage now includes negative-false `for` local
  initialization, with a native differential match and 1,480 total rows.

- Refreshed the generated Python coverage page after the measured dead-yield
  slice moved one row from refusal to match.

- Generator functions now admit the measured first `next()` of a dead
  expression-position `yield` assignment; live send-value use remains loud.

- C++ callable-frame coverage now includes negative-false while zero-iteration
  initialization, with a native differential match and 1,479 total rows.

- Clarified that the reusable Python meta-theorems, including
  `PayloadBlind.lean`, remain in lean-surfaces even though the sunfish proof
  artifacts live in the separate sunfish repository.

- C++ callable-frame coverage now includes negative-false while local
  initialization, with a native differential match and 1,478 total rows.

- C++ callable-frame coverage now includes negative-false while local
  initialization `return`, with a native differential match and 1,477 total
  rows.

- C++ callable-frame coverage now includes negative-false while local
  initialization `break`, with a native differential match and 1,476 total
  rows.

- C++ callable-frame coverage now includes negative-false while local
  initialization `continue`, with a native differential match and 1,475 total
  rows.

- C++ callable-frame coverage now includes negative-false literal switch
  initialization, with a native differential match and 1,474 total rows.

- Python's Pass 0 extractor now keeps an unguarded function-body
  `from`-import of an absent module loud, while preserving the measured
  direct guarded fallback path; the import refusal census is drift-free.

- C++ callable-frame coverage now includes negative-false default-switch
  initialization return, with a native differential match and 1,473 total
  rows.

- C++ callable-frame coverage now includes negative-false default-switch
  initialization, with a native differential match and 1,472 total rows.

- C++ callable-frame coverage now includes negative-false literal switch
  initialization assignment return, with a native differential match and
  1,471 total rows.

- C++ callable-frame coverage now includes negative-false literal switch
  initialization return, with a native differential match and 1,470 total rows.

- C++ callable-frame coverage now includes negative-false default-switch
  initialization assignment return, with a native differential match and
  1,469 total rows.

- C++ callable-frame coverage now includes negative-false default-switch
  fallthrough assignment return, with a native differential match and 1,468
  total rows.

- C++ callable-frame coverage now includes negative-false default-switch
  fallthrough assignment, with a native differential match and 1,467 total
  rows.

- C++ callable-frame coverage now includes negative-false default-arm literal
  switch initialization assignment, with a native differential match and
  1,466 total rows.

- C++ callable-frame coverage now includes negative-false literal switch
  initialization assignment, with a native differential match and 1,465 total
  rows.

- C++ callable-frame coverage now includes negative-false switch fallthrough,
  with a native differential match and 1,464 total rows.

- C++ callable-frame coverage now includes negative-false nested-shadow switch
  fallthrough, with a native differential match and 1,463 total rows.

- C++ callable-frame coverage now includes negative-false `for`
  initialization-assignment fallthrough, with a native differential match and
  1,462 total rows.

- F-string formatting now admits lowercase binary `b` for bounded integer and
  Boolean fields through the intrinsic format worker.

- F-string formatting now admits lowercase character `c` for bounded integer
  and Boolean fields, including explicit surrogate values.

- The measured dynamic f-string format code `q` now preserves CPython's exact
  invalid-format `ValueError`; richer format grammar remains loud.

- `yield from` generator expressions whose target is used later now preserve
  the private target scope through a synthesized helper generator.

- F-string formatting now admits lowercase octal `o` for bounded integer and
  Boolean fields through the intrinsic format worker.

- F-string formatting now admits lowercase hexadecimal `x` for bounded integer
  and Boolean fields through the existing intrinsic format worker.

- C++ callable-frame coverage now includes negative-false `while`
  initialization-assignment fallthrough, with a native differential match and
  1,461 total rows.

- C++ callable-frame coverage now includes false-condition declaration-initialized
  `for` assignment `break`, with a native differential match and 1,458 total rows.

- C++ callable-frame coverage now includes negative-false do-while
  initialization-assignment fallthrough, with a native differential match and
  1,460 total rows.

- C++ callable-frame coverage now includes negative-input declaration-initialized
  `for` assignment `break`, with a native differential match and 1,459 total rows.

- Plain imports of an inventory-absent, unaliased module now take the exact
  `ModuleNotFoundError` path at executable scopes; present modules and other
  import shapes remain loud.

- Exception handlers now recognize CPython's `UnicodeEncodeError` and
  `UnicodeTranslateError` names, completing the Unicode exception-name table;
  payload-bearing constructors remain outside the tier.

- Python f-strings now admit one-field dynamic format specifications by
  evaluating the nested field and reusing the existing intrinsic numeric
  format grammar; multi-part and richer specifications remain loud.

- Corrected the generated Python coverage page to report the implemented
  `NotImplemented` singleton as a modelled constant rather than a refused
  builtin name.

- Reconciled the Python architecture and family registry: the monadic
  interpreter is the tier definition, while theorem statements remain over
  `Semantics.lean` until the owed `twinAgrees` adequacy edge is proved.

- Refreshed the generated README language-progress table after the C++ lane
  advanced to 1,425 of 1,442 checked rows.

- Refreshed the generated README language-progress table after the C++ lane
  added eight differential rows, bringing its checked-in total to 1,420 of
  1,437.

- Refreshed the generated Python coverage page and README language-progress
  table after the proof-interpreter generator-cell guard increased proof-side
  matches to 3,813 of 3,946 rows.

- The Python proof-side generator-expression guard now refuses leaked walrus
  captures, conditional captures, and captures rebound after creation instead
  of silently using a stale value; the exception shadowing smoke guards again
  pin their intentional loud refusals while the monadic runner keeps its live
  cell semantics.

- C++ callable-frame coverage now includes a negative-false do-while
  initialization-assignment `return` path, with a native differential match
  and 1,420 total rows.

- C++ callable-frame coverage now includes a negative-false do-while
  initialization-assignment `continue` path, with a native differential match
  and 1,421 total rows.

- C++ callable-frame coverage now includes a negative-false do-while
  initialization-assignment `break` path, with a native differential match
  and 1,422 total rows.

- C++ callable-frame coverage now includes a negative-false `for`
  initialization-assignment path, with a native differential match and 1,423
  total rows.

- C++ callable-frame coverage now includes a negative-false `for`
  initialization-assignment `return` path, with a native differential match
  and 1,424 total rows.

- C++ callable-frame coverage now includes a negative-false `for`
  initialization-assignment `continue` path, with a native differential match
  and 1,425 total rows.

- C++ callable-frame coverage now includes a negative-false `for`
  initialization-assignment `break` path, with a native differential match and
  1,426 total rows.

- C++ callable-frame coverage now includes a negative zero-iteration `while`
  computed-initialization `continue` path, with a native differential match
  and 1,427 total rows.

- C++ callable-frame coverage now includes a negative zero-iteration `while`
  computed-initialization `break` path, with a native differential match and
  1,428 total rows.

- C++ callable-frame coverage now includes a negative zero-iteration `while`
  computed-initialization `return` path, with a native differential match and
  1,429 total rows.

- C++ callable-frame coverage now includes a negative zero-iteration `while`
  computed-initialization path, with a native differential match and 1,430
  total rows.

- C++ callable-frame coverage now includes a negative-input plain `for`
  initialization-assignment path, with a native differential match and 1,431
  total rows.

- C++ callable-frame coverage now includes a negative-input plain `for`
  initialization-assignment `return` path, with a native differential match
  and 1,432 total rows.

- C++ callable-frame coverage now includes a negative-input plain `for`
  initialization-assignment `continue` path, with a native differential match
  and 1,433 total rows.

- C++ callable-frame coverage now includes a negative-input plain `for`
  initialization-assignment `break` path, with a native differential match and
  1,434 total rows.

- C++ callable-frame coverage now includes negative-input plain `for`
  initialization-assignment fallthrough, with a native differential match and
  1,435 total rows.

- C++ callable-frame coverage now includes skipped-body plain `for`
  initialization-assignment fallthrough, with a native differential match and
  1,436 total rows.

- C++ callable-frame coverage now includes direct plain `for`
  initialization-assignment fallthrough, with a native differential match and
  1,437 total rows.

- C++ callable-frame coverage now includes direct do-while
  initialization-assignment fallthrough, with a native differential match and
  1,438 total rows.

- C++ callable-frame coverage now includes false-condition do-while
  initialization-assignment fallthrough, with a native differential match and
  1,439 total rows.

- C++ callable-frame coverage now includes negative-input do-while
  initialization-assignment fallthrough, with a native differential match and
  1,440 total rows.

- C++ callable-frame coverage now includes direct while
  initialization-assignment fallthrough, with a native differential match and
  1,441 total rows.

- C++ callable-frame coverage now includes false-condition while
  initialization-assignment fallthrough, with a native differential match and
  1,442 total rows.

- C++ callable-frame coverage now includes negative-input while
  initialization-assignment fallthrough, with a native differential match and
  1,443 total rows.

- C++ callable-frame coverage now includes negative-input declaration-initialized
  `for` body fallthrough, with a native differential match and 1,444 total rows.

- C++ callable-frame coverage now includes a skipped declaration-initialized
  `for` body with negative input, with a native differential match and 1,445
  total rows.

- C++ callable-frame coverage now includes negative-input declaration-initialized
  `for` `continue`, with a native differential match and 1,446 total rows.

- C++ callable-frame coverage now includes negative-input declaration-initialized
  `for` `break`, with a native differential match and 1,447 total rows.

- C++ callable-frame coverage now includes negative-input declaration-initialized
  `for` `return`, with a native differential match and 1,448 total rows.

- C++ callable-frame coverage now includes false-condition declaration-initialized
  `for` `return`, with a native differential match and 1,449 total rows.

- C++ callable-frame coverage now includes negative-input declaration-initialized
  `for` assignment, with a native differential match and 1,450 total rows.

- C++ callable-frame coverage now includes false-condition declaration-initialized
  `for` assignment, with a native differential match and 1,451 total rows.

- C++ callable-frame coverage now includes false-condition declaration-initialized
  `for` `continue`, with a native differential match and 1,452 total rows.

- C++ callable-frame coverage now includes false-condition declaration-initialized
  `for` `break`, with a native differential match and 1,453 total rows.

- C++ callable-frame coverage now includes negative-input declaration-initialized
  `for` assignment `return`, with a native differential match and 1,454 total rows.

- C++ callable-frame coverage now includes false-condition declaration-initialized
  `for` assignment `return`, with a native differential match and 1,455 total rows.

- C++ callable-frame coverage now includes false-condition declaration-initialized
  `for` assignment `continue`, with a native differential match and 1,457 total rows.

- C++ callable-frame coverage now includes negative-input declaration-initialized
  `for` assignment `continue`, with a native differential match and 1,456 total rows.

- C++ callable-frame coverage now includes a negative-false do-while
  initialization-assignment path, with a native differential match and 1,419
  total rows.

- C++ callable-frame coverage now includes a negative-false while
  initialization-assignment `break` path, with a native differential match
  and 1,418 total rows.

- C++ callable-frame coverage now includes a negative-false while
  initialization-assignment `continue` path, with a native differential match
  and 1,417 total rows.

- C++ callable-frame coverage now includes a negative-false while
  initialization-assignment `return` path, with a native differential match
  and 1,416 total rows.

- C++ callable-frame coverage now includes a negative-false while
  initialization-assignment path, with a native differential match and 1,415
  total rows.

- C++ callable-frame coverage now includes a negative-false do-while single
  computed-initialization path, with a native differential match and 1,414
  total rows.

- C++ callable-frame coverage now includes a negative-false do-while
  computed-initialization `break` path, with a native differential match and
  1,413 total rows.

- C++ callable-frame coverage now includes a negative-false do-while
  computed-initialization `return` path, with a native differential match and
  1,412 total rows.

- C++ callable-frame coverage now includes a negative-false do-while
  computed-initialization `continue` path, with a native differential match
  and 1,411 total rows.

- C++ callable-frame coverage now includes a negative-false do-while
  computed-initialization path, with a native differential match and 1,410
  total rows.

- C++ callable-frame coverage now includes a negative-false while computed
  initialization `return` path, with a native differential match and 1,409
  total rows.

- C++ callable-frame coverage now includes a negative-false while computed
  initialization `break` path, with a native differential match and 1,408
  total rows.

- C++ callable-frame coverage now includes a negative-false while computed
  initialization `continue` path, with a native differential match and 1,407
  total rows.

- C++ callable-frame coverage now includes a negative-false while computed
  initialization path, with a native differential match and 1,406 total rows.

- C++ callable-frame coverage now includes a negative-false while-shadow
  computed-initialization assignment path, with a native differential match
  and 1,405 total rows.

- C++ callable-frame coverage now includes a negative-false while-shadow
  computed-initialization assignment-`break` path, with a native differential
  match and 1,404 total rows.

- C++ callable-frame coverage now includes a negative-false while-shadow
  computed-initialization assignment-`continue` path, with a native
  differential match and 1,403 total rows.

- The Python axiom census now runs independent import-family scans concurrently
  with a bounded worker pool, preserving deterministic receipt merging while
  avoiding a serial cascade of legacy proof imports in full CI.

- C++ callable-frame coverage now includes a negative-false while-shadow
  computed-initialization assignment-return path, with a native differential
  match and 1,402 total rows.

- C++ callable-frame coverage now includes a negative-input while-shadow
  computed-initialization assignment-return path, with a native differential
  match and 1,401 total rows.

- C++ callable-frame coverage now includes a negative-false while-shadow
  computed-initialization `return` path, with a native differential match and
  1,400 total rows.

- C++ callable-frame coverage now includes a negative-false while-shadow
  computed-initialization `break` path, with a native differential match and
  1,399 total rows.

- C++ callable-frame coverage now includes a negative-false while-shadow
  computed-initialization `continue` path, with a native differential match
  and 1,398 total rows.

- C++ callable-frame coverage now includes a negative-false while-shadow
  computed-initialization path, with a native differential match and 1,397
  total rows.

- C++ callable-frame coverage now includes a negative-false while
  shadow-initialization assignment-continue path, with a native differential
  match and 1,396 total rows.

- C++ callable-frame coverage now includes a negative-input while
  shadow-initialization assignment-continue path, with a native differential
  match and 1,395 total rows.

- C++ callable-frame coverage now includes a negative-false while
  shadow-initialization assignment-return path, with a native differential
  match and 1,394 total rows.

- C++ callable-frame coverage now includes a negative-input while
  shadow-initialization assignment-return path, with a native differential
  match and 1,393 total rows.

- C++ callable-frame coverage now includes a negative-false while
  shadow-initialization assignment-break path, with a native differential
  match and 1,392 total rows.

- C++ callable-frame coverage now includes a negative-input while
  shadow-initialization assignment-break path, with a native differential
  match and 1,391 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  while shadow initialization-assignment, with a native differential match
  and 1,390 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while shadow initialization-assignment, with a native differential match
  and 1,389 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  while shadow initialization, with a native differential match and 1,388
  total rows.

- The Python axiom census now separates incompatible import closures before
  scanning and merges their receipts, so mixed umbrella/legacy proof roots no
  longer fail on duplicate generated equation declarations.

- C++ callable-frame coverage now includes a negative-input companion for
  while shadow initialization, with a native differential match and 1,387
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  while shadow computed initialization with a single assignment, with a
  native differential match and 1,386 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while shadow computed initialization with a single assignment, with a
  native differential match and 1,385 total rows.

- The Python interpreter smoke tests now expect the first-class callable values
  produced for functions and builtins, keeping the umbrella test module aligned
  with the current name-resolution semantics.

- The legacy `GenBound` proof target now states its nested-generator closure
  allocation under the explicit no-cell-directory condition required by the
  current recursive-closure model, restoring its standalone build.

- The reusable `DictCalc` key-normal-form proof now covers the current value
  model, including lone surrogates and callable values, so its standalone
  proof target builds again.

- The legacy `PayloadBlind` generator-locality proof now builds again after the
  `RVal` payload constructors and cell-store cases were brought up to date;
  the VCGen and `tri` proof targets are green.

- The surrogate `%c` formatting branch now uses a list-based singleton helper,
  so the theorem elaborator can generate equality lemmas for `py_simp` and the
  `tri` proof quickstart remains buildable.

- Python strings now retain lone UTF-16 surrogate code points from `chr` and
  `%c`, matching CPython; the runner serializes them as canonical `\uXXXX`
  escapes at the JSON boundary.

- First-class callable values now cross the internal value boundary as named
  callables. Functions, classes, namedtuple classes, and builtin names remain
  loud when observed or called, while the runner reports their CPython
  `unmappable` boundary types (`function`, `type`, or
  `builtin_function_or_method`) exactly.

- Nested functions may now call themselves recursively through an initialized
  closure cell. The extractor and both interpreters fill the self cell with
  the allocated closure before its first call; first-class callable values at
  the public boundary remain loud.

- The Python runner now carries the starting key order through explicit
  `iter(dict)` cursors as well as `for` loops, so the measured silent
  same-size churn path agrees with CPython; the theorem interpreter keeps
  explicit iterator churn loud.

- The Python runner now tracks a dictionary cursor's starting key order. Same-size
  delete/reinsert churn follows CPython's compact-table behavior: a cursor that
  has run off the end completes silently, while a remaining entry raises the
  measured `RuntimeError: dictionary keys changed during iteration`; the proof
  interpreter retains its conservative refusal for this stateful cursor.

- C++ callable-frame coverage now includes a negative-false companion for
  the false-initializer return path, with a native differential match and 1,357
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  zero-iteration computed continue, with a native differential match and
  1,357 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  zero-iteration computed break, with a native differential match and 1,358
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  zero-iteration computed return, with a native differential match and 1,359
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  zero-iteration computed initialization, with a native differential match
  and 1,360 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while-loop computed initialization, with a native differential match and
  1,361 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while-loop computed initialization with `continue`, with a native
  differential match and 1,362 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while-loop computed initialization with `break`, with a native differential
  match and 1,363 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while-loop computed initialization with `return`, with a native
  differential match and 1,364 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while-loop initialization-assignment, with a native differential match and
  1,365 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while-loop initialization-assignment with `return`, with a native
  differential match and 1,366 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while-loop initialization-assignment with `continue`, with a native
  differential match and 1,367 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while-loop initialization-assignment with `break`, with a native
  differential match and 1,368 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  do-while initialization-assignment, with a native differential match and
  1,369 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  do-while initialization-assignment with `return`, with a native
  differential match and 1,370 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  do-while initialization-assignment with `continue`, with a native
  differential match and 1,371 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  do-while initialization-assignment with `break`, with a native differential
  match and 1,372 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  do-while computed initialization, with a native differential match and
  1,373 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  do-while computed initialization with `continue`, with a native
  differential match and 1,374 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  do-while computed initialization with `break`, with a native differential
  match and 1,375 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  do-while computed initialization with `return`, with a native
  differential match and 1,376 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  do-while single computed initialization, with a native differential match
  and 1,377 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while shadow computed initialization, with a native differential match and
  1,378 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while shadow computed initialization with `continue`, with a native
  differential match and 1,379 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while shadow computed initialization with `break`, with a native
  differential match and 1,380 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while shadow computed initialization with `return`, with a native
  differential match and 1,381 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while shadow computed initialization-assignment, with a native differential
  match and 1,382 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while shadow computed initialization-assignment with `continue`, with a
  native differential match and 1,383 total rows.

- C++ callable-frame coverage now includes a negative-input companion for
  while shadow computed initialization-assignment with `break`, with a native
  differential match and 1,384 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  for-loop computed initialization, with a native differential match and 1,356
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  zero-iteration computed continue, with a native differential match and 1,355
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  zero-iteration computed return, with a native differential match and 1,354
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  zero-iteration computed break, with a native differential match and 1,353
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  zero-iteration computed initialization, with a native differential match and
  1,352 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  for-loop computed assignment-break, with a native differential match and
  1,351 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  for-loop computed assignment-continue, with a native differential match and
  1,350 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  for-loop computed assignment, with a native differential match and 1,349
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  for-loop computed return, with a native differential match and 1,348 total
  rows.

- C++ callable-frame coverage now includes a negative-false companion for
  for-loop computed assignment-return, with a native differential match and
  1,347 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  plain conditional-else computed assignment-return, with a native
  differential match and 1,346 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  plain conditional-else computed initialization, with a native differential
  match and 1,345 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  conditional-else computed shadow initialization, with a native differential
  match and 1,344 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  conditional computed shadow initialization, with a native differential
  match and 1,343 total rows.

- The Python runner now preserves late-bound captures of assigned locals in
  generator expressions. Synthetic generator frames receive shared `<cell>`
  parameters, and assignments update the shared heap cell, so rebinding before
  a generator consumer and an unbound conditional capture agree with CPython;
  the theorem interpreter keeps generator-cell modules loud until its
  stateful generator proof surface is widened.

- C++ callable-frame coverage now includes a negative-false companion for
  conditional-else computed shadow assignment, with a native differential
  match and 1,342 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  conditional-else computed shadow assignment-return, with a native
  differential match and 1,341 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  conditional computed shadow assignment-return, with a native differential
  match and 1,340 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  conditional computed shadow assignment, with a native differential match
  and 1,339 total rows.

- The Python runner now preserves PEP 572 walrus bindings that escape a
  generator expression through a shared closure cell. The theorem interpreter
  records this generator-cell shape as loud until its value semantics are
  widened.

- C++ callable-frame coverage now includes a negative-false companion for
  conditional-else shadow initialization, with a native differential match
  and 1,338 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  conditional shadow initialization, with a native differential match and
  1,337 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch-default shadow fallthrough assignment-return, with a native
  differential match and 1,336 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch-default shadow fallthrough assignment, with a native differential
  match and 1,335 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch-default shadow return, with a native differential match and 1,334
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch-default shadow assignment-return, with a native differential match
  and 1,333 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow return, with a native differential match and 1,332 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow assignment-return, with a native differential match and 1,331
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow assignment, with a native differential match and 1,330 total
  rows.

- The Python tier now models CPython's `NotImplemented` singleton as a
  truthy, identity-stable, hashable value. Builtin lookup, equality, rendering,
  dictionary keys, and the proof interpreter are covered; unsupported operations
  remain loud.

- C++ callable-frame coverage now includes a negative-false companion for
  switch default shadow assignment, with a native differential match and
  1,329 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch default shadow initialization, with a native differential match and
  1,328 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow fallthrough assignment, with a native differential match and
  1,327 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow fallthrough initialization, with a native differential match
  and 1,326 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow initialization, with a native differential match and 1,325
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  single-assignment `do while` shadow computed initialization, with a native
  differential match and 1,324 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  `do while` shadow computed initialization with assignment and `return`,
  with a native differential match and 1,323 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  `do while` shadow computed initialization with assignment and `break`,
  with a native differential match and 1,322 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  `do while` shadow computed initialization with assignment and `continue`,
  with a native differential match and 1,321 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  `do while` shadow computed initialization with assignment, with a native
  differential match and 1,320 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  `do while` shadow computed initialization with `return`, with a native
  differential match and 1,319 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  `do while` shadow computed initialization with `break`, with a native
  differential match and 1,318 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  `do while` shadow computed initialization with `continue`, with a native
  differential match and 1,317 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  `do while` shadow computed initialization, with a native differential
  match and 1,316 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  `do while` shadow initialization, with a native differential match and
  1,315 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  zero-iteration `while` shadow computed initialization, with a native
  differential match and 1,314 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  zero-iteration `for` shadow computed initialization, with a native
  differential match and 1,313 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow computed assignment, with a native differential match and
  1,312 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow computed assignment-return, with a native differential match
  and 1,311 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow computed return, with a native differential match and 1,310
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow computed fallthrough assignment-return, with a native
  differential match and 1,309 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow computed fallthrough assignment, with a native differential
  match and 1,308 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow computed fallthrough initialization, with a native
  differential match and 1,307 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  switch shadow computed initialization, with a native differential match and
  1,306 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  default shadow computed fallthrough assignment-return, with a native
  differential match and 1,305 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  default shadow computed fallthrough assignment, with a native differential
  match and 1,304 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  default shadow computed return, with a native differential match and 1,303
  total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  default shadow computed assignment-return, with a native differential match
  and 1,302 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  default shadow computed assignment, with a native differential match and
  1,301 total rows.

- C++ callable-frame coverage now includes a negative-false companion for
  default shadow computed initialization, with a native differential match and
  1,300 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default computed assignment-plus-return false path, with a native
  differential match and 1,299 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default computed fallthrough assignment-plus-return path, with a
  native differential match and 1,298 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default computed fallthrough assignment path, with a native
  differential match and 1,297 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default computed-shadow assignment-plus-return path, with a native
  differential match and 1,296 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default computed-shadow fallthrough assignment-plus-return path, with
  a native differential match and 1,295 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default computed-shadow fallthrough assignment path, with a native
  differential match and 1,294 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default computed-shadow return path, with a native differential match
  and 1,293 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default computed-shadow return-false path, with a native differential
  match and 1,292 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default computed-shadow initialization false path, with a native
  differential match and 1,291 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default computed-shadow initialization path, with a native differential
  match and 1,290 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch computed-shadow return-false path, with a native differential match and
  1,289 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch computed-shadow initialization false path, with a native differential
  match and 1,288 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch computed-shadow fallthrough assignment-plus-return false path, with a
  native differential match and 1,287 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch computed-shadow fallthrough assignment false path, with a native
  differential match and 1,286 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch computed-shadow fallthrough assignment-plus-return path, with a native
  differential match and 1,285 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch computed-shadow fallthrough assignment path, with a native differential
  match and 1,284 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch computed-shadow assignment-plus-return false path, with a native
  differential match and 1,283 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch computed-shadow assignment-plus-return path, with a native differential
  match and 1,282 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch computed-shadow return path, with a native differential match and
  1,281 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch computed-shadow initialization path, with a native differential match
  and 1,280 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  zero-iteration `for` computed-shadow continue-false path, with a native
  differential match and 1,279 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  zero-iteration `for` computed-shadow continue path, with a native differential
  match and 1,278 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  zero-iteration `for` computed-shadow return path, with a native differential
  match and 1,277 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  zero-iteration `for` computed-shadow break path, with a native differential
  match and 1,276 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  zero-iteration `for` computed-shadow initialization path, with a native
  differential match and 1,275 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  `for` computed-shadow return-false path, with a native differential match and
  1,274 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  `for` computed-shadow assignment-break path, with a native differential match
  and 1,273 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  `for` computed-shadow assignment-continue path, with a native differential
  match and 1,272 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  `for` computed-shadow assignment-false path, with a native differential match
  and 1,271 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  plain `for` computed-shadow initialization path, with a native differential
  match and 1,270 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  `for` computed-shadow return path, with a native differential match and 1,269
  total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  `for` computed-shadow assignment-plus-return path, with a native differential
  match and 1,268 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  conditional else computed-shadow assignment path, with a native differential
  match and 1,267 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  conditional else computed-shadow assignment-plus-return path, with a native
  differential match and 1,266 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed conditional else-shadow assignment-plus-return path, with a native
  differential match and 1,265 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed conditional assignment-plus-return path, with a native differential
  match and 1,264 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed conditional else-shadow assignment path, with a native differential
  match and 1,263 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed conditional shadow assignment path, with a native differential match
  and 1,262 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed conditional else-shadow initialization path, with a native
  differential match and 1,261 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed conditional shadow initialization path, with a native differential
  match and 1,260 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  conditional else-shadow initialization path, with a native differential match
  and 1,259 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  conditional shadow initialization path, with a native differential match and
  1,258 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow switch assignment-plus-return path, with a native differential
  match and 1,257 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow switch assignment path, with a native differential match and
  1,256 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow switch fallthrough-assignment return path, with a native
  differential match and 1,255 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow switch fallthrough-assignment path, with a native differential
  match and 1,254 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow switch fallthrough path, with a native differential match and
  1,253 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed default-shadow switch return path, with a native differential match
  and 1,252 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow switch return path, with a native differential match and
  1,251 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed default-shadow switch fallthrough-assignment return path, with a
  native differential match and 1,250 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed default-shadow switch fallthrough-assignment path, with a native
  differential match and 1,249 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed default-shadow switch assignment-plus-return path, with a native
  differential match and 1,248 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed default-shadow switch assignment path, with a native differential
  match and 1,247 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed default-shadow switch initialization path, with a native differential
  match and 1,246 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow switch initialization path, with a native differential match
  and 1,245 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default-shadow initialization fallthrough-assignment return path, with
  a native differential match and 1,244 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default-shadow initialization fallthrough-assignment path, with a
  native differential match and 1,243 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default-shadow initialization assignment-plus-return path, with a
  native differential match and 1,242 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default-shadow initialization return path, with a native differential
  match and 1,241 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch shadow initialization return path, with a native differential match
  and 1,240 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch shadow initialization assignment-plus-return path, with a native
  differential match and 1,239 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch shadow initialization assignment path, with a native differential
  match and 1,238 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default-shadow initialization assignment path, with a native
  differential match and 1,237 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch default-shadow initialization path, with a native differential match
  and 1,236 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch shadow initialization fallthrough-assignment path, with a native
  differential match and 1,235 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch shadow initialization fallthrough path, with a native differential
  match and 1,234 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  switch shadow initialization path, with a native differential match and
  1,233 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow do-while single-assignment path, with a native differential
  match and 1,232 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow do-while assignment-plus-`return` path, with a native
  differential match and 1,231 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow do-while assignment-plus-`break` path, with a native
  differential match and 1,230 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow do-while assignment-plus-`continue` path, with a native
  differential match and 1,229 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow do-while assignment path, with a native differential match
  and 1,228 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow do-while `return` path, with a native differential match and
  1,227 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow do-while `break` path, with a native differential match and
  1,226 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow do-while `continue` path, with a native differential match
  and 1,225 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  computed shadow do-while path, with a native differential match and 1,224
  total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  do-while shadow initialization path, with a native differential match and
  1,223 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  `for` shadow computed-initialization zero-iteration path, with a native
  differential match and 1,222 total rows.

- C++ callable-frame coverage now includes a negative-value companion for the
  while shadow computed-initialization zero-iteration path, with a native
  differential match and 1,221 total rows.

- C++ callable-frame coverage now includes a zero-value companion for the
  non-nested shadow computed-initialization `for` zero-iteration path, with a
  native differential match and 1,220 total rows.

- C++ callable-frame coverage now includes a zero-value companion for the
  nested shadow computed-initialization `for` zero-iteration path, with a
  native differential match and 1,219 total rows.

- C++ callable-frame coverage now includes the false zero-iteration companion
  for nested shadow computed initialization with `break`, with a native
  differential match and 1,218 total rows.

- C++ callable-frame coverage now includes the false zero-iteration companion
  for nested shadow computed initialization with `continue`, with a native
  differential match and 1,217 total rows.

- C++ callable-frame coverage now includes a guarded pre-increment whose false
  branch preserves the initialized value, with a native differential match and
  1,216 total rows.

- C++ callable-frame coverage now includes a guarded local declaration whose
  false branch preserves the parameter result, with a native differential match
  and 1,215 total rows.

- C++ callable-frame coverage now includes a guarded shadowing local whose
  false branch preserves the outer initialized value, with a native differential
  match and 1,214 total rows.

- C++ callable-frame coverage now includes a guarded parameter-based local
  initialization whose false branch preserves the parameter result, with a
  native differential match and 1,213 total rows.

- C++ callable-frame coverage now includes a guarded post-decrement whose false
  branch preserves the initialized value, with a native differential match and
  1,212 total rows.

- C++ callable-frame coverage now includes a guarded decrement whose false
  branch preserves the initialized value, with a native differential match and
  1,211 total rows.

- C++ callable-frame coverage now includes a guarded post-increment whose false
  branch preserves the initialized value, with a native differential match and
  1,210 total rows.

- C++ callable-frame coverage now includes a guarded compound local assignment
  whose false branch preserves the initialized value, with a native differential
  match and 1,209 total rows.

- C++ callable-frame coverage now includes a conditional local assignment
  whose false branch preserves the initialized value, with a native differential
  match and 1,208 total rows.

- Bare `FileNotFoundError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing filesystem
  error constructors remain outside the tier.

- Bare `FloatingPointError` raises now use the admitted builtin exception
  identity and are caught by `except ArithmeticError:`; payload-bearing
  arithmetic-error constructors remain outside the tier.

- Bare `InterruptedError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing filesystem
  error constructors remain outside the tier.

- Bare `IsADirectoryError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing filesystem
  error constructors remain outside the tier.

- Bare `NotADirectoryError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing filesystem
  error constructors remain outside the tier.

- Bare `NotImplementedError` raises now use the admitted builtin exception
  identity and are caught by `except RuntimeError:`; payload-bearing runtime
  error constructors remain outside the tier.

- Bare `PermissionError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing filesystem
  error constructors remain outside the tier.

- Bare `ProcessLookupError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing filesystem
  error constructors remain outside the tier.

- Bare `ReferenceError` raises now use the admitted builtin exception identity
  and are caught by `except Exception:`; payload-bearing reference-error
  constructors remain outside the tier.

- Bare `TimeoutError` raises now use the admitted builtin exception identity
  and are caught by `except OSError:`; payload-bearing filesystem-error
  constructors remain outside the tier.

- `UnicodeDecodeError` is now admitted as an exception handler name; its
  payload-bearing constructor remains outside the tier.

- Bare `MemoryError` raises now use the admitted builtin exception identity
  and are caught by `except Exception:`; payload-bearing memory-error
  constructors remain outside the tier.

- Bare `FileExistsError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing filesystem
  error constructors remain outside the tier.

- Bare `ConnectionResetError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing connection
  error constructors remain outside the tier.

- Bare `ConnectionRefusedError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing connection
  error constructors remain outside the tier.

- Bare `ConnectionError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing connection
  error constructors remain outside the tier.

- Bare `ConnectionAbortedError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing connection
  error constructors remain outside the tier.

- Bare `ChildProcessError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing process-error
  constructors remain outside the tier.

- Bare `BytesWarning` raises now use the admitted builtin exception identity
  and are caught by `except Warning:`; payload-bearing warning constructors
  remain outside the tier.

- Bare `BufferError` raises now use the admitted builtin exception identity
  and are caught by `except Exception:`; payload-bearing buffer-error
  constructors remain outside the tier.

- Bare `BrokenPipeError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing I/O error
  constructors remain outside the tier.

- Bare `BlockingIOError` raises now use the admitted builtin exception
  identity and are caught by `except OSError:`; payload-bearing I/O error
  constructors remain outside the tier.

- Bare `UnboundLocalError` raises now use the admitted builtin exception
  identity and are caught by `except NameError:`; payload-bearing local-name
  error constructors remain outside the tier.

- Bare `SystemError` raises now use the admitted builtin exception identity
  and are caught by `except Exception:`; payload-bearing system-error
  constructors remain outside the tier.

- Bare `TabError` raises now use the admitted builtin exception identity and
  are caught by `except IndentationError:`; payload-bearing syntax error
  constructors remain outside the tier.

- Bare `IndentationError` raises now use the admitted builtin exception
  identity and are caught by `except SyntaxError:`; payload-bearing syntax
  error constructors remain outside the tier.

- Bare `EOFError` raises now use the admitted builtin exception identity
  and are caught by `except Exception:`; payload-bearing end-of-file
  constructors remain outside the tier.

- Bare `SyntaxError` raises now use the admitted builtin exception identity
  and are caught by `except Exception:`; payload-bearing syntax-error
  constructors remain outside the tier.

- Bare `SyntaxWarning` raises now use the admitted builtin exception identity
  and are caught by `except Warning:`; payload-bearing warning constructors
  remain outside the tier.

- Bare `ResourceWarning` raises now use the admitted builtin exception
  identity and are caught by `except Warning:`; payload-bearing warning
  constructors remain outside the tier.

- Bare `PendingDeprecationWarning` raises now use the admitted builtin
  exception identity and are caught by `except Warning:`; payload-bearing
  warning constructors remain outside the tier.

- Bare `ImportWarning` raises now use the admitted builtin exception identity
  and are caught by `except Warning:`; payload-bearing warning constructors
  remain outside the tier.

- Bare `FutureWarning` raises now use the admitted builtin exception identity
  and are caught by `except Warning:`; payload-bearing warning constructors
  remain outside the tier.

- Bare `DeprecationWarning` raises now use the admitted builtin exception
  identity and are caught by `except Warning:`; payload-bearing warning
  constructors remain outside the tier.

- Bare `RuntimeWarning` raises now use the admitted builtin exception identity
  and are caught by `except Warning:`; payload-bearing warning constructors
  remain outside the tier.

- Bare `UserWarning` raises now use the admitted builtin exception identity
  and are caught by `except Warning:`; payload-bearing warning constructors
  remain outside the tier.

- Bare `UnicodeWarning` raises now use the admitted builtin exception identity
  and are caught by `except Warning:`; payload-bearing warning constructors
  remain outside the tier.

- Bare `UnicodeError` raises now use the admitted builtin exception identity
  and are caught by `except Exception:`; payload-bearing Unicode error
  constructors remain outside the tier.

- Bare `Warning` raises now use the admitted builtin exception identity and are caught by `except Exception:`; payload-bearing warning constructors remain outside the tier.

- The generated Python coverage page now counts the separately modelled `ImportError` and `ModuleNotFoundError` handler identities alongside the admitted builtin exception table.

- The generated Python coverage page now lists every admitted builtin exception identity, including `SystemExit`, `KeyboardInterrupt`, and `GeneratorExit`, instead of treating generic matcher fallbacks as refusals.

- Bare `StopAsyncIteration` raises now use the admitted builtin exception identity and are caught by `except Exception:`; payload-bearing constructors remain outside the tier.

- `EnvironmentError` and `IOError` now raise and match as CPython's canonical
  `OSError` identity, including exact alias handler coverage.

- The generated Python coverage page now records the admitted bare import
  exception identities accurately, including their payload boundary.

- Bare `ImportError` and `ModuleNotFoundError` raises now use the admitted
  builtin exception identity and are caught by `except Exception:`; payload
  constructors and direct import-handler matching remain loud.

- The clock-erasure proof now follows the cached function-scope `TypeError`
  handler census, including its synthetic no-op marker and retained-frame
  local/shadow checks, so the complete Python proof target builds again.

- Payload-blind proofs now preserve the TypeError handler census across the
  heap-swapped frame, restoring the full proof and quickstart build after the
  handler-resolution change.

- Callable plain-`for` declaration initializers now preserve body-local assignment effects before loop exit, including the enclosing frame's returned value.

- Callable plain-`for` declaration initializers now retain the enclosing value when a false loop condition skips a body-local assignment.

- Callable plain-`for` declaration initializers now return the body-local assignment result before leaving the loop body.

- Callable plain-`for` declaration initializers now preserve the enclosing return value when a false loop condition skips a body-local assignment and return.

- Callable plain-`for` declaration initializers now retain body-local assignment effects across `continue` and the loop step.

- Callable plain-`for` declaration initializers now retain body-local assignment effects across `break`.

- Callable plain-`for` declaration initializers now retain the enclosing value when a false condition skips a body-local assignment and `break`.

- Callable plain-`for` declaration initializers now retain the enclosing value when a false condition skips a body-local assignment and `continue`.

- Do-while declaration initializers now preserve body-local assignment results when the post-body condition is false before a `return`.

- Do-while declaration initializers now preserve body-local assignment results across `continue` when the initial condition is false.

- Do-while declaration initializers now preserve body-local assignment results across `break` when the initial condition is false.

- While declaration initializers now preserve the enclosing value when a false condition skips the body-local assignment.

- While declaration initializers now preserve the enclosing return value when a false condition skips a body-local assignment and `return`.

- While declaration initializers now preserve the enclosing value when a false condition skips a body-local assignment and `continue`.

- While zero-computed initialization now preserves the computed local assignment before `break`.

- While zero-computed initialization now preserves the computed local assignment before `return`.

- While zero-computed initialization now preserves the computed local assignment across `continue`.

- For zero-computed initialization now preserves the computed local assignment before `break`.

- For zero-computed initialization now preserves the computed local assignment before `return`.

- For zero-computed initialization now preserves the computed local assignment across `continue`.

- Switch computed initialization now returns the computed local directly from a matching case.

- Switch computed initialization now preserves the enclosing value when the returning case is skipped.

- Switch default computed initialization now returns the computed local directly from the default arm.

- Switch default computed initialization now preserves the enclosing value when the returning default arm is skipped.

- Switch default computed initialization now preserves an assignment through fallthrough to the following case.

- Switch default computed initialization now preserves the enclosing value when the fallthrough default arm is skipped.

- Switch default computed initialization now records the enclosing return after fallthrough assignment.

- Switch default computed initialization now preserves the enclosing return when fallthrough assignment is skipped.

- Switch default initialization now preserves a constant assignment through fallthrough to the following case.

- Switch default constant initialization now preserves the enclosing value when the default arm is skipped before fallthrough.

- Range slicing now composes the source progression exactly, including
  negative slice steps, empty results, and CPython's slice validation errors;
  the resulting immutable range remains available at the public boundary.

- Nested function definitions inside loops now use the enclosing frame's
  shared closure cell, matching CPython's late-bound capture on each call;
  unsupported deeper scopes and generator rebinding edges remain loud.

- TypeError-handler local analysis is now computed once during ingestion and
  marked only on affected functions, keeping ordinary proof reductions fast
  while preserving the handler's late-binding behavior.

- Function-scope `except TypeError` handlers now resolve after the protected
  body, reproducing CPython's invalid-handler `TypeError` and late-binding
  `UnboundLocalError` while preserving the existing loud boundary for other
  dynamically shadowed exception classes.

- The triad classifier self-test now uses an isolated SystemVerilog fixture,
  so adding a cross-tier example import cannot change the test's one-tier
  expectation.

- The clock-erasure proof now tracks starred positional arguments, static-local
  markers, faithful missing-local errors, exception-handler dispatch, and the
  current context-manager exit arguments across the stateful interpreter.

- README now renders one progress bar per supported language from the checked-in
  coverage pages; CI fails when the percentages or row counts go stale.

- Module-level exception handlers now resolve their class after the protected
  body runs, matching CPython when the body rebinds a handler name and emits
  the faithful `TypeError` for a non-exception class.

- The `divmod_lab` proof now keeps its symbolic integer theorem on a bounded
  simplification path; the float `divmod` case remains covered by its kernel
  `#py_check` and the dedicated `float_lab` proof, avoiding a duplicate
  high-memory reduction in hosted CI.

- Hosted full CI now gives each Python Lean source file its own Lake process,
  releasing elaboration state between proof and spec targets to keep the full
  gate below the runner's resource limit.

- The `bench_statistics` acceptance guards now record the faithful
  `NameError` raised when its intentionally unvendored `StatisticsError`
  name is reached on empty input.

- The clock-trace example now checks the modeled `AttributeError` for a
  shadowed `time` receiver, keeping its non-vacuity guard aligned with the
  interpreter.

- Hosted full CI now builds each Python example directory in its own Lake
  process, releasing proof state between examples so late Python targets are
  not killed by accumulated memory pressure.

- Hosted full CI now isolates each `Examples/<language>` source group in its
  own Lake process, preventing late Python proof targets from inheriting the
  memory pressure of unrelated example groups.

- Hosted full CI now builds each declared default target in its own Lake
  process, preserving the complete gate while releasing accumulated build
  state between target groups.

- Hosted full CI now uses one Lean elaboration worker, preserving the complete
  repository gate while avoiding the runner resource kill at the final Python
  targets.

- The `rsa_inverse` proof now composes a nested `extended_gcd` call through
  the stateful `CallsIn` judgment without weakening the conservative
  heap-free fragment.

- Flat starred `for` targets now reuse the existing starred-unpack worker for
  each loop item; nested and otherwise unsupported target shapes remain loud.
- Decimal `int(str)` conversion now returns CPython's pinned 4300-digit `ValueError` instead of a tier refusal; malformed inputs within the budget retain their exact literal errors.
- A generator's safe `try: yield <scalar literal or parameter> except Stop: pass` shape now lowers to the existing continuation and matches CPython; yield expressions that can raise and other suspendable `try` forms remain loud.
- Bare-name `del` in function scope now installs the static-local marker that CPython uses: reads after deletion, deleting a module-global or never-bound name, and a second deletion all raise the faithful `UnboundLocalError` while earlier deletions retain their partial effect.
- Bare `raise OSError` now uses the existing empty builtin class-identity exception path; payload-bearing and OS-derived constructors, plus direct `EnvironmentError`, remain loud.
- Raising an ordinary scalar parameter, including a parameter that shadows a builtin exception, now preserves CPython's `TypeError: exceptions must derive from BaseException`; late or rebound locals and heap-backed values remain loud.
- A single direct assignment before a local exception raise now follows the same dynamic scalar path; late or rebound assignments retain their static-local refusal.
- Module-level `del` now erases an unobserved static definition or benign-import binding as a safe no-op; later reads keep the loud static-table refusal.
- Deleting the script runner's `__name__` now exposes CPython's `builtins` fallback; other module dunders remain loud.
- A bare builtin exception raise before one direct local assignment now reports CPython's `UnboundLocalError`; branch-local and repeated shadows remain loud.
- A same-list scalar `append` in an effectful `finally` now runs before the returned list is published; other cleanup shapes remain loud.
- Tuple unpacking now stores a constant-key dictionary subscript element through the existing heap path; other non-name target shapes remain loud.
- Attribute-first chained assignment now names the RHS once in an unspellable temporary before left-to-right stores; other non-name-first chains remain loud.
- Starred displays now lower through unspellable `<star-tuple>` and `<star-list>` builtin markers, so ordinary `list`/`tuple` bindings cannot shadow the generated calls; local and sibling-scope displays both remain live.
- Direct calls of a nested function before its definition now raise CPython's faithful `UnboundLocalError` through the frame's static-local marker; ordinary dynamically shadowed calls remain loud.
- Starred set displays now lower through the existing `<star-list>` expansion and `set(...)` constructor; set results remain boundary-loud while observations such as `len({*a})` match CPython.
- Starred positional call arguments now expand eager iterables in place through an unspellable `<star-arg>` marker, preserving source order and CPython's argument errors; keyword unpacking and other unsupported iterable shapes remain loud.
- Synchronous context managers now admit the exact `__exit__(self, exc_type, exc, tb): return exc_type is not None` suppression test, passing a fixed exception marker on exceptional body paths; arbitrary exception-triple inspection remains loud.
- Context managers may define `__repr__` without losing the supported protocol; other extra dunders remain loud.
- `is` and `is not` now decide booleans and CPython 3.9's cached small integers from `-5` through `256`; larger or otherwise implementation-dependent immediate identities remain loud.
- Direct `repr()` of a class instance now admits the exact `__repr__(self): return "literal"` shape; richer custom rendering and instance rendering in containers remain loud.
- Direct `bool()` of a class instance now admits the exact `__bool__(self): return False` or `True` literal shape; richer custom truthiness remains loud.
- Class instances now admit the exact two-parameter Boolean-literal `__eq__` shape; richer custom equality remains loud.
- Unknown exception constructor names now raise CPython's exact `NameError` before constructor arguments are evaluated; known but unmodelled builtins and shadowed names remain loud.
- Container `repr` and `ascii` rendering now use a fixed 512-level depth budget; deeper structures remain loud independently of caller fuel.
- Python `global` declarations now support direct scalar reads, assignments, and
  augmented assignments across function frames, with module-global publication
  preserved by the script runner.
- Direct scalar `nonlocal` declarations now update and reread shared closure
  cells; unsupported compound scope forms remain loud.
- The class tier now admits a single plain-name base from an earlier
  same-module class, resolving inherited methods and `__init__`; unresolved,
  forward, multiple, dynamic, and external bases remain loud.
- Explicit `class C(object)` now uses the existing default-protocol instance
  semantics; other external and dynamic bases remain loud.
- Direct subclasses of the measured builtin exception names now preserve their
  class identity through `raise` and explicit handler matching; shadowed,
  dynamic, and unmeasured exception bases remain loud.
- Plain tuples of admitted exception names now share one retained-state handler
  body; dynamic exception expressions, shadowed tuple names, and multiple
  handler suites remain loud.
- `raise N from None` now lowers to the existing class-identity raise because
  exception causes are not observable in the tier; dynamic causes remain loud.
- Function-local value-less annotations now install a static-local marker and
  raise CPython's exact `UnboundLocalError` class and message on an observed
  read, including declarations in skipped branches; harmless no-read forms
  remain erased. The harness no longer normalizes this subclass to
  `NameError`.

All notable changes to the **Python tier** of this repository (the extractor,
the Lean semantics under `LeanModels/Python/`, its proof surface, and its
tools). The other tiers (SystemVerilog, C++, RISC-V) are versioned separately
and are not covered here.

The public surface these entries track is listed in
[docs/reference.md § Public surface and stability](docs/reference.md#public-surface-and-stability-0x).
While the version is 0.x, a minor release may change that surface; every such
change is listed here under **Changed** or **Removed**.

## [Unreleased]

## [0.1.17] — 2026-10-29

### Changed

- String percent formatting now admits the measured heap-dict mapping slice:
  `'%(k)s' % {'k': 1}` performs literal string-key lookup and scalar
  conversion, while `'abc' % {'k': 1}` follows CPython's mapping leftover
  rule and returns `'abc'`; rich mapping syntax remains loud.
- Literal f-string format specifications `d`, `>5`, and `03d` now run for
  integer and Boolean fields through a shared synthetic format worker. Dynamic,
  multi-part, and richer format mini-language forms remain loud.
- `float([])` and other heap values without an admitted `__float__` protocol now
  raise CPython's faithful non-numeric `TypeError`; custom conversion protocols
  remain loud.
- The non-callable `iter(v, sentinel)` path now raises CPython's faithful
  `TypeError: iter(v, w): v must be callable`; callable iterator construction
  remains loud.
- The grammar's complex-literal witness now matches for the exact direct
  `print(1j)` observation.  The runtime keeps complex values themselves loud,
  so non-print uses and other spellings remain outside the modeled value tier.
- `try … except … else` now runs its `else` suite after a normal body exit.
  The extractor lowers the construct to the existing retained-state `try`
  node plus a fresh success flag and `if`; `finally`, tuple patterns, and
  observed exception bindings remain loud. A measured two-handler slice with
  scalar-literal returns is lowered to nested retained-state `try` nodes in
  source order; wider handler suites remain loud.
- `except (A, B, …)` now admits tuples of plain, admitted exception names and
  matches each member against the existing builtin and user-class tables.
  Dynamic expressions, shadowed names, and multiple handler suites remain
  loud.
- `raise N from None` now lowers to `raise N`; the tier keeps dynamic exception
  causes loud because it does not model exception-cause payloads.
- A direct `try: raise N; except N: raise` now re-raises the statically known
  class identity; broad and dynamic bare re-raises remain loud.
- Single-target `del o.attr` now lowers through the synthetic `<attrdel>`
  operation. The monadic interpreter deletes ordinary instance attributes
  in place and preserves CPython's `AttributeError` for missing and immediate
  receivers; the proof interpreter keeps the heap mutation loud.
- Immediate float NaN equality now follows IEEE/CPython semantics (`nan ==
  nan` is `False`, and `!=` is `True`) without requiring arithmetic payload
  propagation; NaN ordering and hashing remain loud.
- Float ordering now follows CPython's unordered NaN comparisons: `<` returns
  `False` when either operand is NaN, and stable sorting keeps the input order.

- The fixed decimal parsing and rendering budget is now 4300 digits. `int`,
  `str`, `print`, f-strings, percent formatting, and nested container, range,
  and namedtuple rendering admit the pinned CPython default boundary and refuse larger values.
- The integer three-argument `pow` builtin now handles positive moduli and
  nonnegative and bounded negative exponents, including the faithful
  zero-modulus and non-invertible-base `ValueError`s.
- Heap-backed `list * int` and `int * list` now allocate fresh repeated lists
  on the monadic interpreter, with CPython's index-size and materialization
  bounds; the value-side proof interpreter keeps this stateful shape loud.
- Boundary `Val.list` snapshots now support ordinary `list * int` and
  `int * list` in the pure value interpreter, including length-only
  observation without materializing an over-budget result; heap-list aliasing
  and augmented repetition remain stateful.
- The alias-free parameter shape `x *= count; return x` now lowers at
  ingestion to the same pure repetition path for boundary lists. Alias-bearing
  and control-flow augmented mutations remain loud until the H2 heap boundary
  flip.
- Heap-backed list `*=` now updates the existing list address in place on the
  monadic interpreter, so aliases observe the repeated contents; the proof
  interpreter keeps this stateful mutation loud.
- Attribute reads and unknown method calls on immediate scalar receivers now
  raise CPython's faithful `AttributeError` instead of stopping at the
  heap-receiver boundary; admitted scalar methods remain unchanged.
- `int(str)` now admits CPython's Unicode decimal digits and whitespace through
  the shared float-text normalization table; malformed non-decimal Unicode
  now raises CPython's exact `ValueError` instead of a tier refusal.
- `float(bytes)` now accepts ASCII decimal bytes through the shared float-text
  parser and preserves CPython's bytes-rendered conversion errors; non-ASCII
  bytes and NaN payload spellings remain loud.
- `float("nan")` now accepts canonical case-insensitive textual NaN forms,
  preserving CPython's quiet-NaN word and explicit sign bit. Payload spellings
  remain loud; ordinary binary `+`, `-`, and `*` now quiet NaN inputs while
  preserving their payload/sign, and use the pinned canonical negative quiet
  NaN for invalid infinity combinations. Float floor division, modulo, and
  `divmod`, and true division apply the same propagation and zero-denominator
  priority.
- `str.join()` now consumes admitted heap generators, preserving their lazy
  state and CPython's indexed element validation.
- Monadic `itertools.count` now admits integer, Boolean, and binary64 start/step
  values through a value-carrying generator frame, preserving CPython's
  first-value subtype and numeric addition on both interpreter surfaces.
  NaN payloads quiet on the first step and infinities remain stable.
- String case methods now admit Latin-1 input characters, including CPython's
  `µ`, `ß` → `SS`, and `ÿ` → `Ÿ` mappings; characters outside Latin-1 remain
  loud until the full Unicode case tables are represented.
- String `repr` renders printable Latin-1 characters directly, with exact
  `\xNN` escapes for C1 controls, NBSP, and soft hyphen; the Unicode table
  extension below covers code points above Latin-1.
- String `repr` now follows CPython 3.9's Unicode 13.0 printability table:
  printable code points such as `λ` and `😀` render directly, while controls,
  separators, unassigned, and private-use code points use exact `\\uNNNN` or
  `\\UNNNNNNNN` escapes. `%r`, f-string repr conversion, and nested container
  rendering share this table.
- `dict()` now accepts pair sequences from immediate and heap-backed lists,
  tuples, bytes, strings, and namedtuples, preserving CPython's ordered
  length, hashability, and duplicate-key checks.
- `iter(bytes)` now creates a lazy immutable byte cursor; `next()` yields
  integer octets and exhaustion follows the existing `StopIteration` behavior.
- The measured bare `b"%s" % bytes` form now copies its bytes operand;
  other bytes formatting syntax remains loud.
- `time.time(...)` now evaluates positional arguments and raises CPython's
  exact arity `TypeError` without consuming the trace; the zero-argument
  trace-clock call remains the admitted form.
- Container `repr` and `ascii` rendering now use a fixed 512-level depth
  budget; deeper structures remain loud independently of caller fuel.
- `format(value, "d")` now admits the bare decimal specification for integer
  and Boolean values through the fixed decimal renderer; other non-empty
  format specifications remain loud.
- Mixed immediate scalar ordering in `sorted`, `max`, `min`, and comparisons
  now raises CPython's exact `TypeError` payload; heap and unsupported protocol
  comparisons remain loud.
- F-string `!a` fields now use the shared ASCII renderer on both interpreter
  surfaces; non-empty format specifications and custom protocols remain loud.
- Non-simple annotated assignment targets now evaluate their annotation and
  perform the ordinary attribute or subscript store in CPython order; class
  annotations and observed value-less declarations remain loud.
- Heap-list-valued attribute `+=` now extends the existing list address in
  place for deterministic list, tuple, string, bytes, and range operands;
  stateful and hash-order iterables remain loud.
- Subscripting an escaped dictionary view now raises CPython's exact
  `TypeError` for its concrete view type instead of an internal refusal.
- Escaped dictionary views now render their exact CPython type-specific
  `dict_keys([...])`, `dict_values([...])`, or `dict_items([...])` representation;
  set algebra beyond the admitted key-view intersection and other unsupported
  protocols remain loud.
- Two escaped `dict_keys` views over the same dictionary now compare equal;
  key-view/set intersection now allocates a fresh set, while values-view
  equality, item-view set algebra, and other set operators remain loud.
- String repetition counts beyond the pinned CPython index-sized range now
  raise the exact `OverflowError`, including empty strings and nonpositive
  counts; positive materialization-budget refusals remain loud.
- Length-only `len(sequence * count)` repetition now computes the CPython
  length for strings, bytes, tuples, and namedtuples without materializing an
  over-budget result. Direct expressions and the admitted temporary-assignment
  forms preserve index overflow, nonpositive and empty short-circuits, and
  faithful sequence `TypeError`s.
- Admitted user exception classes now preserve one positional string argument,
  matching CPython's uncaught `Stop: message` output; non-string and
  multi-argument constructors remain loud.
- Integer left-shift counts at the conservative measured overflow guard now
  raise CPython's exact `OverflowError: too many digits in integer`; ordinary
  counts beyond the fixed materialization budget remain loud.
- Integer decimal rendering beyond the pinned 4300-digit limit now raises
  CPython's exact `ValueError` and message across scalar, format, f-string,
  container, and script rendering paths.
- Bare `%s` and `%r` formatting now renders ref-free tuple, namedtuple, range,
  and boundary-list operands with CPython's deterministic container spelling;
  heap references and mapping-key formatting remain loud.
- Refreshed the exception ancestor example envelope so `raise BaseException()`
  uses the admitted zero-argument class-identity path and matches CPython.
- Unused `except Class as name` bindings are now admitted by erasing the
  unobservable temporary; reads of the exception object remain loud.
- `SystemExit`, `KeyboardInterrupt`, and `GeneratorExit` now have builtin
  class-identity raises and are caught by `BaseException`; they remain outside
  `Exception`, and uncaught process-exit behavior remains outside the function
  boundary.
- `OSError` and its `EnvironmentError` alias are now admitted handler names;
  represented non-OS errors propagate through them, while direct OS raises and
  actual OS effects remain outside the tier.
- A single bare `except:` now catches every represented exception; multiple
  handlers, tuple patterns, and observed exception bindings remain loud.
- Direct top-level expression and assignment references now raise the faithful
  runtime `NameError` when they occur before a later definition; compound
  statements retain their conservative control-shell admission guard.

## [0.1.16] — 2026-10-28

### Added

- Immediate local aliases of supported builtins now preserve CPython's
  name-resolution and call behavior for `abs`, `all`, `any`, `ascii`, `bin`,
  `chr`, `float`, `format`, `hex`, `int`, `len`, `list`, `max`, `min`, `next`,
  `oct`, `ord`, `pow`, `print`, `range`, `repr`, `round`, `sorted`, `str`,
  `sum`, and `tuple`; returned and first-class callable aliases remain loud.
- Flat starred `for` targets, safe generator yields under `try`, and the
  measured decimal conversion boundary now follow CPython with faithful
  errors and evaluation order.

### Fixed

- Proof-side frames for marked locals and the cached-small-integer identity
  regression guard now match the admitted semantics. The Python differential
  suite has **3,756 rows**, with **3,712 matches / 44 recorded refusals** in
  the executable runner and **3,603 matches / 153 refusals** in the proof
  interpreter; the grammar census has **145 witnesses, 136 MATCH and 9
  REFUSE**.

## [0.1.15] — 2026-10-26

### Added

- Exception control flow now covers `try … except … else`, measured multiple
  handlers, tuple patterns, direct re-raises, empty `OSError`, scalar raise
  errors, and safe generator yields under `try`; dynamic payloads and wider
  handler forms remain loud.
- Starred assignment targets, starred positional calls, and starred set
  displays now reuse the existing eager unpacking paths with CPython's
  evaluation order and errors.
- Float NaN equality and ordering, Unicode integer parsing, literal f-string
  format specifications, and the fixed 512-level container renderer now
  follow the measured CPython behavior.
- Direct global/nonlocal updates, simple class inheritance and object bases,
  class protocol methods, dictionary-view operations, sequence repetition, and
  the exact synchronous context-manager suppression form are admitted.
- Immediate local aliases of `bool` and `divmod`, plus unread assignments of
  admitted exception classes, ordinary classes, and module functions, are
  erased at ingestion when their values are not observed.

### Fixed

- Proof-side monotonicity, clock-erasure, payload-blind, builtin-dispatch,
  and generator-dispatch walkers now track the corresponding semantic arms.
- The measured Python differential suite now has **3,695 rows**, with **3,651
  matches / 44 recorded refusals** in the executable runner and **3,542
  matches / 153 refusals** in the proof interpreter; the grammar census has
  **145 witnesses, 136 MATCH and 9 REFUSE**.

## [0.1.14] — 2026-10-21

### Added

- Flat starred assignments such as `head, *middle, tail = values` now drain
  the right-hand iterable and bind a fresh list for the middle slice. Nested,
  multiple, non-name, and starred `for` targets remain loud.
- Bare-name list item deletion now follows CPython for integer and Boolean
  indices, including negative indices, missing-item `IndexError`, and the
  faithful non-integer index `TypeError`.
- First-class dictionary `keys()`, `values()`, and `items()` views retain their
  source dictionary and observe later mutations through supported length,
  membership, and consuming-iteration paths. `enumerate` over the values and
  items views now retains the view kind and yields the corresponding elements.

### Fixed

- Proof-side clock-erasure and payload-blind walkers now cover the dictionary
  view object and its backing reads while preserving their refusal-safe
  behavior.
- The measured Python differential suite now has **3,538 rows**, with **3,206
  matches / 332 recorded refusals** in the executable runner and **3,119
  matches / 419 refusals** in the proof interpreter; the grammar census has
  **144 witnesses, 130 MATCH and 14 REFUSE**.

## [0.1.13] — 2026-10-21

### Added

- `int(text, base)` and `int(text, base=base)` accept ASCII strings and bytes
  in bases 2–36, plus base-zero prefix detection, signs and underscores.
  Both interpreters preserve CPython's argument evaluation, arity, keyword,
  base validation and invalid-literal errors. Unicode parsing, non-ASCII
  bytes, heap conversion protocols and inputs beyond the digit budget remain
  unfinished and refuse loudly.
- `repr`, `abs`, `ord`, `chr`, `next`, `ascii`, `tuple`, `list`, `range`,
  `hex`, `oct`, and `bin` keyword calls now evaluate arguments in Python order
  before reporting their exact positional-only `TypeError`. `int` validates
  arity and keyword names after argument evaluation. Regression cases check
  retained argument effects and argument exceptions preceding the call error.
- `float(...)` keyword calls now preserve Python's argument evaluation order
  and report the faithful `TypeError` that the constructor accepts no keyword
  arguments; other builtin keyword shapes remain loud.
- `divmod(...)` keyword calls now preserve argument evaluation order and report
  CPython's faithful positional-only `TypeError`; other builtin keyword forms
  remain loud.
- `len(...)` keyword calls now preserve argument evaluation order and report
  CPython's faithful positional-only `TypeError`; other builtin keyword forms
  remain loud.
- `bool(...)` keyword calls now preserve argument evaluation order and report
  CPython's faithful positional-only `TypeError`; other builtin keyword forms
  remain loud.
- Module-scope annotated assignments now admit unshadowed builtin type-name
  annotations such as `x: int = 1`; the value binding is preserved and the
  implicit `__annotations__` update is unobservable in the tier. Shadowed and
  effectful annotation expressions remain loud.
- `int(bytes)` now accepts the ASCII decimal slice shared with `int(str)`,
  including CPython whitespace, signs, underscore grouping, digit-budget
  refusal, and exact bytes-rendered invalid-literal errors. Non-ASCII bytes
  now take that invalid-literal path; bytes methods, decoding, and bytes
  percent formatting remain loud.
- Bare `raise ValueError` and the other 15 admitted builtin exception class
  names now work in both interpreters, including ancestor matching, retained
  effects, and generator closure. `Exception` does not catch `BaseException`;
  `StopIteration` escaping a generator becomes `RuntimeError` (PEP 479).
  Direct zero-argument constructors such as `raise ValueError()` now lower to
  the same class-identity path; payload-bearing exception instances, chaining
  and locally shadowed raise names remain loud unfinished work.

### Fixed

- Icarus unavailable-oracle declarations normalize the DUT path in stdout
  as well as stderr, fixing a diagnostic that depended on the local checkout
  directory. Phase-2 failures publish complete escaped GitHub annotations.
- SV envelope regeneration preserves canonical packed select expressions,
  including genvar indices into multidimensional vectors and selects beyond
  default parameter widths. CI runs the extractor regressions and publishes
  failed gate names as annotations.
- SV differential checks report exact, source-bound Icarus disagreements
  separately from matches. Known compiler/runtime limitations remain visible
  as unavailable oracle coverage, with their diagnostics checked on each run;
  changed or resolved declarations require review.
- `tools/leanpy --compare` now compares exception classes as well as stdout
  and exit status, so two different uncaught exceptions cannot be reported as
  a false `MATCH` merely because CPython maps both to exit 1.
- The axiom census limits its directly invoked Lean process to one worker,
  avoiding thread exhaustion on hosts with many hardware threads.
- Recognized namedtuple classes shadow builtin exception names in raises and
  handlers. Both interpreters preserve CPython's distinct `TypeError` messages;
  handler validation occurs only after the body raises, keeping its effects.
- `sum(iterable, start)` now validates the iterable before rejecting a string
  start, matching CPython's error order for non-iterables. String and bytes
  start validation shares one worker, reports default-protocol instance names
  faithfully, and never consumes generators before rejecting the start.

## [0.1.12] — 2026-10-15

### Added

- Immutable bytes literals and literal defaults now preserve every octet through
  extraction and the proof boundary. Both interpreters support bytes indexing,
  slicing, concatenation, repetition, comparisons, membership, rendering,
  unpacking, iteration in loops/comprehensions, and sequence consumers. Bytes
  numeric parsing, explicit iterator cursors, decoding, methods, bytes percent
  formatting, and `dict(bytes)` pair construction remain loud unfinished work.
  The CPython 3.9 differential suite now has **2,840 / 3,174 rows = 89.5%
  complete** natively and **2,766 / 3,174 = 87.2% complete** in the proof
  interpreter, with **100% agreement among decided rows** and zero failures;
  grammar coverage is **123 / 142 = 86.6% complete**.

## [0.1.11] — 2026-10-12

### Added

- The `round()` builtin now models its one-argument integer and Boolean slice,
  including CPython's exact missing-number `TypeError`; float rounding and
  `ndigits` remain loud until their oracle is specified. The CPython 3.9
  differential suite now has **2,760 / 3,086 rows = 89.4% complete** natively
  and **2,686 / 3,086 = 87.0% complete** in the proof interpreter, with **100%
  agreement among decided rows** and zero failures.

- The `format()` builtin now models value-only formatting and an explicit empty
  specification through the shared scalar/container renderer, with faithful
  arity and second-argument errors; non-empty format specifications remain
  loud until the format mini-language is specified. The CPython 3.9
  differential suite now has **2,770 / 3,097 rows = 89.4% complete** natively
  and **2,696 / 3,097 = 87.1% complete** in the proof interpreter, with **100%
  agreement among decided rows** and zero failures.

- Synchronous `with` now supports explicit zero-argument constructors, multiple
  items through nested lowering, and body exception unwinding for transparent
  `__exit__` methods (`pass`, `return None`, or `return False`); the original
  exception and retained state are preserved. Argument-sensitive suppression,
  full exception triples, and `async with` remain loud. The CPython 3.9
  differential suite now has **2,777 / 3,105 rows = 89.4% complete** natively
  and **2,703 / 3,105 = 87.1% complete** in the proof interpreter, with **100%
  agreement among decided rows** and zero failures; grammar coverage is
  **118 / 142 = 83.1% complete** and the script corpus is **84 / 107 = 78.5%
  complete**.

## [0.1.10] — 2026-10-12

### Added

- The SystemVerilog region world now retains edge and absolute-delay waiting
  targets. Supported waiting-target suspension/resume preserves residuals,
  effects, NBA work, and deadlines; unresolved process-control branches remain
  loud.

- The SystemVerilog self-check tier admits ordered `for` and sampled-count
  `repeat` loops with nearest-loop `break`/`continue`. Retained continuation
  markers preserve loop phases across ordinary dependency waits; explicit
  process-control suspension and disputed count conversions stay loud.

- The `ascii()` builtin now renders scalar values and ASCII-escapes Unicode
  strings, with CPython's exact one-argument arity error; heap-recursive
  values remain loud rather than guessing a representation. The CPython 3.9
  differential suite now has **2,755 / 3,081 rows = 89.4% complete** natively
  and **2,681 / 3,081 = 87.0% complete** in the proof interpreter, with **100%
  agreement among decided rows** and zero failures.

- The `bin()` builtin now renders bounded integers and Booleans with
  CPython's lowercase `0b` form, including negative values, faithful
  one-argument arity errors, and integer-required `TypeError`s; heap objects
  and oversized integers remain loud. The CPython 3.9 differential suite now
  has **2,749 / 3,074 rows = 89.4% complete** natively and **2,675 / 3,074 =
  87.0% complete** in the proof interpreter, with **100% agreement among
  decided rows** and zero failures.

- The `oct()` builtin now renders bounded integers and Booleans with
  CPython's lowercase `0o` form, including negative values, faithful
  one-argument arity errors, and integer-required `TypeError`s; heap objects
  and oversized integers remain loud. The CPython 3.9 differential suite now
  has **2,744 / 3,069 rows = 89.4% complete** natively and **2,670 / 3,069 =
  87.0% complete** in the proof interpreter, with **100% agreement among
  decided rows** and zero failures.

- The `hex()` builtin now renders bounded integers and Booleans with
  CPython's lowercase `0x` form, including negative values, faithful
  one-argument arity errors, and integer-required `TypeError`s; heap objects
  and oversized integers remain loud. The CPython 3.9 differential suite now
  has **2,739 / 3,064 rows = 89.4% complete** natively and **2,665 / 3,064 =
  87.0% complete** in the proof interpreter, with **100% agreement among
  decided rows** and zero failures.

- Fixed `%05d` string formatting now zero-pads decimal fields after the sign,
  preserving negative values and over-width numbers. The CPython 3.9
  differential suite now has **2,734 / 3,059 rows = 89.3% complete** natively
  and **2,660 / 3,059 = 86.9% complete** in the proof interpreter, with **100%
  agreement among decided rows** and zero failures.

- Fixed `%-5d` string formatting now left-aligns decimal fields with spaces,
  preserving negative values and over-width numbers. The CPython 3.9
  differential suite now has **2,731 / 3,056 rows = 89.3% complete** natively
  and **2,657 / 3,056 = 86.9% complete** in the proof interpreter, with **100%
  agreement among decided rows** and zero failures.

- Fixed `%5d` string formatting now pads decimal fields with spaces on the
  left without truncation, including negative values and over-width numbers.
  The CPython 3.9 differential suite now has **2,728 / 3,053 rows = 89.3%
  complete** natively and **2,654 / 3,053 = 86.9% complete** in the proof
  interpreter, with **100% agreement among decided rows** and zero failures.

- Bare `%a` string formatting now uses CPython's ASCII-escaped `repr`,
  including `\\x`, `\\u`, and `\\U` escapes for non-ASCII strings. The CPython
  3.9 differential suite now has **2,725 / 3,051 rows = 89.3% complete**
  natively and **2,651 / 3,051 = 86.8% complete** in the proof interpreter,
  with **100% agreement among decided rows** and zero failures.

- Bare `%u` string formatting now follows the bounded decimal integer path,
  preserving negative values and CPython's `%u`-specific TypeError wording.
  The CPython 3.9 differential suite now has **2,719 / 3,045 rows = 89.3%
  complete** natively and **2,645 / 3,045 = 86.8% complete** in the proof
  interpreter, with **100% agreement among decided rows** and zero failures.

- Bare `%o` string formatting now renders bounded lowercase octal for
  integers and Booleans, including negative values, with CPython's faithful
  integer-required `TypeError` for other scalar types. The CPython 3.9
  differential suite now has **2,715 / 3,041 rows = 89.3% complete** natively
  and **2,641 / 3,041 = 86.8% complete** in the proof interpreter, with **100%
  agreement among decided rows** and zero failures.

- Bare `%c` string formatting now accepts integer code points and
  one-character strings, with CPython's exact `OverflowError` and type-error
  behavior. Lone surrogate code points remain a loud Lean-`Char` boundary.
  The CPython 3.9 differential suite now has **2,711 / 3,037 rows = 89.3%
  complete** natively and **2,637 / 3,037 = 86.8% complete** in the proof
  interpreter, with **100% agreement among decided rows** and zero failures.

- Bare `%i` string formatting now shares the bounded integer conversion and
  CPython's exact TypeError wording with `%d`, including Boolean and negative
  values. The CPython 3.9 differential suite now has **2,705 / 3,030 rows =
  89.3% complete** natively and **2,631 / 3,030 = 86.8% complete** in the
  proof interpreter, with **100% agreement among decided rows** and zero
  failures.

- Invalid `%q` string formats now raise CPython's faithful
  `ValueError: unsupported format character 'q' (0x71) at index 1` instead of
  refusing. The CPython 3.9 differential suite now has **2,701 / 3,026 rows =
  89.2% complete** natively and **2,627 / 3,026 = 86.8% complete** in the
  proof interpreter, with **100% agreement among decided rows** and zero
  failures.

- Trailing `%` string formats now raise CPython's faithful
  `ValueError: incomplete format` instead of refusing. The CPython 3.9
  differential suite now has **2,700 / 3,026 rows = 89.2% complete**
  natively and **2,626 / 3,026 = 86.8% complete** in the proof interpreter,
  with **100% agreement among decided rows** and zero failures.

- Bare `%x` string formatting now renders bounded lowercase hexadecimal for
  integers and Booleans, including negative values, with CPython's faithful
  integer-required `TypeError` for other scalar types. The CPython 3.9
  differential suite now has **2,699 / 3,026 rows = 89.2% complete** natively
  and **2,625 / 3,026 = 86.7% complete** in the proof interpreter, with
  **100% agreement among decided rows** and zero failures.

- Empty and non-positive string, tuple, and namedtuple repetitions now
  short-circuit after the pinned 64-bit `Py_ssize_t` conversion instead of
  tripping the materialization budget. Positive nonempty results remain
  bounded by `seqBudget`, and counts too large for the index-sized conversion
  stay loud. The CPython 3.9 differential suite now has **2,698 / 3,026 rows
  = 89.2% complete** natively and **2,624 / 3,026 = 86.7% complete** in the
  proof interpreter, with **100% agreement among decided rows** and zero
  failures.

- Very large arithmetic right shifts now saturate by the operand's bit length,
  returning `0` for nonnegative operands and `-1` for negative operands instead
  of refusing after `shiftBudget`; negative counts retain the faithful
  `ValueError`. The CPython 3.9 differential suite now has **2,674 / 3,026
  rows = 88.4% complete** natively and **2,600 / 3,026 = 85.9% complete** in
  the proof interpreter, with **100% agreement among decided rows** and zero
  failures.

- Range-to-range equality now compares the produced integer sequences without
  materializing them: empty ranges compare equal, singleton steps are ignored,
  and longer ranges require equal starts, lengths, and steps. The differential
  suite now has **2,652 / 3,016 rows = 87.9% matched**, or **87.9% complete**,
  with **100% agreement among decided rows**.

- Integer subscripting on `range` now follows CPython's sequence indexing,
  including negative indices, stepped ranges, faithful `IndexError`, and the
  range-specific non-integer `TypeError`. The differential suite now has
  **2,657 / 3,020 rows = 88.0% matched**, or **88.0% complete**, with **100%
  agreement among decided rows**.

- Range membership now checks arithmetic progression containment without
  materializing the range, including Boolean and integral-float probes. The
  differential suite now has **2,661 / 3,023 rows = 88.0% matched**, or
  **88.0% complete**, with **100% agreement among decided rows**.

- Range unpacking now uses the bounded materializer for ordinary tuple/list
  targets, preserving stepped values and CPython's exact arity errors. The
  differential suite now has **2,664 / 3,025 rows = 88.1% matched**, or
  **88.1% complete**, with **100% agreement among decided rows**.

- `range` values now cross the public call boundary as structural
  `Val.range` snapshots. The boundary preserves each constructor field's
  integer-or-Boolean form while the runner compares CPython's normalized
  integer attributes. The differential suite now has **2,665 / 3,025 rows =
  88.1% matched**, or **88.1% complete** (proof interpreter: **2,592 / 3,025
  = 85.7%**), with **100% agreement among decided rows**.

- Heap-list slices now follow CPython's step-first validation, allocate a
  fresh list object, and cross the public boundary as `Val.list` snapshots;
  tuple, namedtuple, string, and value-list slices retain their value-level
  behavior. The native differential suite now has **2,668 / 3,025 rows =
  88.2% matched**, or **88.2% complete**; the proof interpreter has **2,594 /
  3,025 = 85.8% complete**, with **100% agreement among decided rows**.

- Negative integer powers now return rounded binary64 reciprocals through the
  shared pure worker, including the faithful `0 ** -1` exception; exponents
  beyond the fixed `floatPowBudget` remain loud. Native differential coverage
  is now **2,671 / 3,025 = 88.3% complete**; proof-interpreter coverage is
  **2,597 / 3,025 = 85.9% complete**, with **100% agreement among decided
  rows**.

- Function-local value-less annotations are erased when no load or delete can
  observe their static-local binding; observed forms remain loud to preserve
  `UnboundLocalError` behavior. Native differential coverage is now **2,672 /
  3,025 = 88.3% complete**; proof-interpreter coverage is **2,598 / 3,025 =
  85.9% complete**, with **100% agreement among decided rows**.

### Fixed

- Python development now has `./check.sh --python-only`, covering both
  interpreters, scripts, refusal/coverage/axiom checks, tooling, docs, and
  Python notebooks without other language harnesses. Default repository CI
  stays full-scope. Measured differential completion is unchanged at
  **2,755 / 3,081 = 89.4%** natively and **2,681 / 3,081 = 87.0%** in the
  proof interpreter, with **100% agreement among decided rows**.
- CI regression guards and refusal inventories now reflect the implemented
  negative-power, empty-repetition, fixed-width formatting, and scalar
  `ascii()` tiers. Repetition proofs keep their original statements, and
  payload-blindness covers the shared pure builtin arm. Measured differential
  completion remains **2,755 / 3,081 = 89.4%** natively and **2,681 / 3,081 =
  87.0%** in the proof interpreter, with **100% agreement among decided rows**.

### Validation

- CPython 3.9 differential suite: **3,081 rows / 2,755 matched / 326 recorded
  refusals / zero mismatches**, so **89.4% of the suite is complete**. The proof
  interpreter matches **2,681 / 3,081 = 87.0%** and refuses 400, also with
  zero mismatches; agreement among decided rows is **100%**.
- Grammar census: **142 witnesses / 117 MATCH / 25 REFUSE**. Whole-program
  scripts: **106 / 83 completed-and-matched / 23 loud-blocked / zero failures**.
- The Python-only acceptance driver passed **21/21 gates**, including a fresh
  **974-job targeted build**, refusal/coverage/axiom checks, docs **89/89**, and
  both Python notebooks (**2/2**, 543.5 seconds). Exact-head hosted CI run
  **38245607413** passed its full check and both quickstarts.

## [0.1.9] — 2026-10-11

### Added

- Two-argument integer `pow` calls now share the pure integer exponentiation
  worker with `**` on both Python interpreter surfaces. Negative exponents stay
  loud, `pow(0, -1)` preserves its faithful zero-division exception, and the
  three-argument modulus form refuses explicitly rather than guessing modular
  arithmetic. The differential suite now has **2,647 / 3,012 rows = 87.9%
  matched** with **100% agreement among decided rows**.

- Float floor division, remainder and `divmod` through a shared pure binary64
  worker on both Python interpreter surfaces, preserving rounded operation
  order, quotient snapping, signed zeros, determined infinite-divisor results
  and the distinct zero-divisor messages. Mixed integer conversion retains
  its priority; unresolved NaN payload results remain explicit coverage work.
  At landing, 2,640 of 3,003 differential rows run and match CPython (87.9%
  of the suite; 100% agreement among decided rows).

- Determined infinity results for float and mixed true division on both Python
  interpreter surfaces: signed infinity and signed zero use the operands' sign
  XOR, zero denominators raise before NaN classification, and mixed integer
  conversion overflow keeps its priority. Kernel proofs, real-artifact
  language/script tests and all-exponent differential sweeps cover the new
  behavior. NaN results remain explicit unfinished oracle/model work.

- Binary64 addition, subtraction and multiplication on both Python interpreter
  surfaces, including mixed integer/Boolean conversion order, augmented
  assignment, signed zero, subnormal rounding and overflow to infinity. The
  extracted `float_lab` artifact proves concrete arithmetic results and
  finite-input cancellation; NaN payload/sign propagation remains explicitly
  refused pending its oracle model. Language/script differential rows and
  all-exponent numeric-core sweeps cover the new behavior.

- `float(...)` construction on both interpreter surfaces: zero arguments,
  binary64-word identity, integer/Boolean conversion and exact decimal-string
  parsing with underscores, exponents, Unicode 13.0.0 digits/whitespace,
  infinities, signed zero and subnormal/overflow rounding. Real-artifact proofs
  and CPython 3.9 differential checks cover values, exception messages and
  evaluation order. Shared repr quote selection now traverses the structural
  code-point list, keeping constructor error proofs kernel-reducible. Textual
  NaN payloads, bytes-like inputs, object protocols, keywords and unresolved
  invalid-Unicode repr remain explicit unfinished coverage work.

### Validation

- CPython 3.9 differential suite: **3,012 rows / 2,647 matched / 365 recorded
  refusals / zero mismatches**, so **87.9% of the suite is complete** and
  agreement among decided rows is 100%. The proof interpreter matches **2,574**
  and refuses **438**, also with zero mismatches.
- Grammar census: **142 witnesses / 114 MATCH / 28 REFUSE**. Whole-program
  scripts: **106 / 82 completed-and-matched / 24 loud-blocked / zero failures**.
- The capped full Lake build passed **3,800 jobs**; focused Python proof and
  runner builds, refusal-census regressions **9/9**, coverage freshness, and
  exact-head CI run **38153627730** all passed.

## [0.1.8] — 2026-10-11

### Added

- Binary64 float literals/defaults and true division on both Python interpreter
  surfaces, backed by a kernel-reducible word/rational core rather than native
  floating-point axioms, with typed `PyFloat`/`ToVal` marshalling. Integer ratios
  round directly; mixed division preserves
  integer-conversion order. Signed zero, subnormal ties, overflow, exact mixed
  comparisons, rendering, unary signs, `abs` and `int` have differential tests.
  The extracted `float_lab` artifact has concrete kernel proofs and script tests.
  Other float arithmetic, non-finite division, float keys, methods and NaN
  identity/container ordering remain explicit unfinished coverage work.

### Changed

- `Const`, `Val` and `RVal` add `float`; `BinOp` adds `div`; `PyErr` adds
  distinct true/float zero-division forms and an overflow message. Downstream
  exhaustive matches must handle these constructors. Binary64 boundary values
  use decimal word strings, rejecting out-of-range words rather than truncating.
  Existing judgment and theorem statements retain their signatures.

### Fixed

- Numeric `itertools.count` admission no longer fabricates a nonnumeric
  `TypeError` for floating-point arguments or silently erases a Boolean
  start's first-value subtype under non-unit stepping. Those unmodelled
  frames refuse explicitly; integer/unit-step cases and invalid-argument
  exceptions retain their checked behavior.

- The refusal census shares the differential harness's exact argument transport,
  preserving binary64 words, signed zero, nested values, and Boolean/integer
  distinctions. Importing that transport no longer re-executes an importer's
  arguments. Runner errors remain census failures, not semantic refusals.

### Validation

- CPython 3.9 differential suite: **2,810 cases / 2,466 matched / 344 recorded
  refusals / zero mismatches**. The proof interpreter matches **2,393** and
  refuses **417** on the same cases, also with zero mismatches.
- Grammar census: **142 witnesses / 114 MATCH / 28 REFUSE**. A matched witness
  does not claim every use of a construct is supported; remaining refusals
  are unfinished language-coverage work.
- Float/counter integration: **86 calls / 71 matched / 15 loud / zero failures**
  on each interpreter surface. The standalone numeric-core sweep checks
  **79,716 rows / zero failures** against CPython bit patterns and messages.
- Script corpus: **94 cases / 74 completed-and-matched / 20 loud / zero failures**.
  Extractor **103/103**, refusal-census regressions **9/9**, and documentation
  **89/89** pass. Typed proofs against the real `float_lab` artifact are
  kernel-checked without new or native proof axioms; all three notebooks pass.

## [0.1.7] — 2026-10-10

### Added

- Ellipsis literals (`...`) and the builtin `Ellipsis` value are the same
  truthy singleton. Identity, equality, rendering, parameter defaults,
  dictionary/set keys, and argument/result transport work on both interpreter
  surfaces. Ordinary builtin shadowing stays visible. `ellipsis_lab` adds
  symbolic singleton-return and integer-identity proofs plus differential cases.

- Intrinsic f-string `!r` fields share the existing heap-aware repr renderer.
  Default debug fields and explicit empty format specifications work, and bare,
  `!s`, and `!r` conversions bypass local/module/generator `str` and `repr`
  shadows. The frontend preserves `JoinedStr`/`FormattedValue` instead of
  synthesizing name calls; symbolic proofs and differential cases cover the
  intrinsic and retained field effects. `!a`, nonempty format specifications,
  and custom protocols remain recorded language gaps.

- Call-only builtin `repr(value)` shares the existing heap-aware renderer with
  container printing on both interpreter surfaces: scalar values, ASCII string
  quoting and escapes, tuples, namedtuples, lists, insertion-ordered dictionaries,
  ranges, and active-path container cycles. Arguments evaluate before exact arity
  errors. Keyword calls, first-class builtin values, identity-dependent values,
  hash-ordered sets, non-ASCII repr strings, and existing rendering budgets remain
  loud. The `repr_lab` artifact proves Boolean and bounded integer rendering
  symbolically and checks retained argument effects and ordinary shadowing.

### Changed

- `Const`, `Val`, and `RVal` add an `ellipsis` constructor; downstream exhaustive
  matches must handle it. Public judgments, tactic interfaces, and existing
  theorem statements retain their signatures. Rebuild downstream Lean artifacts
  after upgrading; notebook headers now verify their compiled dependencies.

### Fixed

- Notebook headers are invalidated when the compiler or any transitive compiled
  import changes, even if envelopes and file timestamps stay unchanged. The
  cache verifies the header bytes, rejects unverifiable dependency inventories,
  and never publishes a dependency key that changed during compilation.

- The refusal census classifies all recorded closed-function and script gaps,
  including the recent parsing, repetition, rendering, and exception fixtures.
  CI now runs both inventories and checks regressions for missing classifications
  and model answers to deliberately loud rows; no interpreter behavior or
  differential expectation changes.

### Validation

- CPython 3.9 differential suite: **2,719 cases / 2,390 matched / 329 recorded
  refusals / zero mismatches**. The proof interpreter matches **2,317** and
  refuses **402** on the same cases, also with zero mismatches.
- Grammar census: **142 witnesses / 112 MATCH / 30 REFUSE**. A matched witness
  does not claim every use of its construct is supported; remaining refusals
  are language-coverage work, not permanent scope exclusions.
- Notebook cache checks: **26 unit/wiring regressions** plus a real Lean
  transitive-constructor regression; all three tutorial notebooks pass.

## [0.1.6] — 2026-10-10

### Added

- Named `BaseException`, `ArithmeticError`, and `LookupError` handlers use
  explicit CPython-measured catch relations on both interpreter surfaces.
  Arithmetic handlers catch both division-error forms; lookup handlers catch
  index and key errors. User namesake classes retain priority, lexical shadows
  remain loud, and OS-error ancestors and exception-class values stay outside
  the tier. The `exc_ancestors_lab` artifact proves a caught-error identity
  symbolically and checks subsumption, propagation, and mutation order.
- The proof interpreter and its module executor now catch the same measured
  builtin exception classes as the native interpreter, using the shared
  `builtinExcCatches` table. Handlers resume from the exception's retained
  state; loud refusals and timeouts are never caught. The `exc_handlers_lab`
  artifact pins matching, propagation, mutations, and module-global publication.
  Function-local handler-class bindings refuse under Python's static-locals
  rule, including assignments after the try, rather than silently catching
  the unshadowed builtin class.
- Integral `divmod(numerator, divisor)` uses the same signed floor quotient and
  remainder operations as `//` and `%`, including Boolean operands and faithful
  zero-divisor and arity errors. Argument effects precede conversion/errors;
  nonintegral operands, keyword calls, and first-class builtin values stay loud.
  The `divmod_lab` artifact proves division by one symbolically and kernel-checks
  signed arithmetic and Boolean coercions.
- Generator-expression capture census preserves lexical local bindings even
  when their names also name builtins or module definitions. Parameters,
  assignments, and nested functions shadow builtin calls inside generators;
  the existing safe-capture admission rules remain unchanged.
- Builtin `bool()` and `bool(value)` share the interpreter's existing
  heap-aware truthiness semantics, including containers, default instances,
  closures, and nondraining generator truthiness. Argument effects precede
  conversion and excess-argument errors. Keyword calls and first-class builtin
  type values remain loud; ordinary shadowing remains in force. The `bool_lab`
  artifact proves integer truthiness and Boolean identity symbolically and
  kernel-checks the admitted container/protocol boundary.
- Module-scope annotated assignments with simple targets, values, and scalar
  literal annotations (including forward-reference strings) preserve assignment
  before annotation evaluation, including inside control-flow bodies. Explicit
  annotation-table bindings and nonliteral annotations remain loud; function-local
  annotation erasure is unchanged. Extractor and CPython 3.9 script regressions
  pin the admitted subset and the annotation-table alias boundary. The `ann_lab`
  artifact proves reads of a string-annotated module global symbolically and
  kernel-checks the refusal of a raising annotation.

### Validation

- CPython 3.9 differential suite: **2,446 cases**, with **2,130 matched** and
  **316 recorded refusals**, zero mismatches. The proof interpreter matched
  **2,057 cases**, refused **389**, and reported zero mismatches.
- Script corpus: **85 files**, with **65 matched**, **20 loud refusals**, and
  zero failures. Grammar census: **139 witnesses**, with **108 matched** and
  **31 refusals**; documentation checks stayed **89/89**.
- The fresh full Lean build and unchanged-budget repository check passed with
  no curated Python example depending on `sorry` or native axioms. The release
  keeps public judgments, tactics, and recorded theorem statements unchanged.

## [0.1.5] — 2026-10-10

### Fixed

- Range construction retains Boolean start, stop, and step objects instead of
  erasing them to integers. Shared rendering now agrees with CPython 3.9 for
  `str`, `print`, f-strings, and nested containers; iteration, length, and other
  admitted numerical consumers still use integer projections. A Boolean `True`
  step is omitted from rendering like integer `1`, and `False` still raises the
  faithful zero-step `ValueError`.
- The `range_render` artifact proves the single-argument Boolean rendering
  symbolically and adds differential controls for integer fields, numerical
  consumers, and constructor exceptions. Previously loud range APIs remain loud.

### Validation

- CPython 3.9 differential suite: **2,250 cases**, with **1,973 matched** and
  **277 recorded refusals**, zero mismatches. The proof interpreter matched
  **1,895 cases**, refused **355**, and reported zero mismatches.
- Whole-program survey: **136 files**, **109 matched**, **27 loud refusals**,
  zero divergences. The repository check passed with no native-dependent or
  sorry-dependent curated Python examples.
- The release metadata, README coverage counts, range-rendering artifact, and
  differential controls agree on the Boolean-field behavior; public judgments,
  tactics, and recorded theorem statements remain unchanged.

### Known Limitations

- Range APIs outside the admitted rendering, iteration, length, and numerical
  consumer tier remain loud refusals; no unsupported API is guessed.

## [0.1.4] — 2026-10-10

### Fixed

- Decimal integer rendering shares the configuration-independent 640-digit
  admission used by decimal parsing. `str`, `print`, f-string interpolation,
  nested container and range rendering, and bare `%s`/`%r`/`%d` refuse larger
  magnitudes before converting them, rather than guessing CPython's
  configurable limit or an exception.
  Signs do not consume the budget; boolean and string rendering is unchanged.
- The `decimal_render` example proves scalar decimal output symbolically under
  the magnitude bound and checks the same boundary across rendering routes.
- Tuple and namedtuple repetition checks the original integer count's magnitude
  before handling empty sequences or negative counts. Counts beyond 1,048,576
  refuse loudly instead of returning a wrong empty result or attempting an
  unbounded allocation; the independent output-element budget is unchanged.
  Both operand orders and `*=` share this admission, without guessing a host
  index width, `OverflowError`, or `MemoryError`.
- The `tuple_repeat` example proves symbolic output lengths under the admission
  bounds and checks boolean counts, namedtuple erasure, and shallow aliasing.

### Validation

- CPython 3.9 differential suite: 2,167 cases, 1,890 matched, 277 recorded
  refusals, zero mismatches. The same rows through the proof interpreter:
  1,812 matched, 355 refused, zero mismatches.
- Whole-program corpus: 76 scripts, 59 matched, 17 loud refusals, zero failures.
- The `tuple_repeat` and `decimal_render` artifacts add three symbolic
  theorem pairs, checked without native-computation or `sorry` dependencies
  and included in the curated axiom gate. Public judgments, tactics, and
  previously recorded theorem statements remain unchanged.
- Frozen Linux quickstart: the first `tri` proof builds in 224 seconds, with
  six tutorial companions taking another 38 seconds. Timing includes fresh
  package-source fetching, excludes the already-installed Lean toolchain and
  preparation of the project-source snapshot, and copies no compiled artifacts;
  no foreign tier or Mathlib library is built.

### Known Limitations

- The pre-existing rendering mismatch for Boolean range start/stop fields
  remains unfixed and is not whitelisted as a refusal. The zero-mismatch counts
  above describe the registered suite, not every Python program; see
  [the decimal-rendering boundary](docs/memory-model.md).

## [0.1.3] — 2026-10-09 (tag publication pending)

### Added

- `int(str)` accepts ASCII decimal underscore grouping and all six integer
  whitespace characters. Invalid ASCII literals raise CPython's exact
  repr-rendered, truncated `ValueError` instead of refusing or misquoting it.
  Decimal strings admit at most 640 ASCII digits, independently of the host's
  configuration; larger digit counts, non-ASCII input, and explicit bases
  remain loud.
- String repetition supports both operand orders, boolean counts, and `*=`,
  preserving Unicode code points and exact non-integer count errors. The
  original signed count's magnitude and the output's code-point length must
  each be at most 1,048,576; heap operands and oversized counts remain loud.
- The new `int_string` and `string_repeat` examples prove symbolic results
  for grouped and signed decimal literals, both repetition operand orders,
  decorated strings, and width arithmetic.
- A repository-root `check.sh` entry point for the existing local CI checks.

### Fixed

- The build protocol inspects Linux log descriptors without requiring `lsof`,
  retains the portable fallback, and refuses when inspection is unavailable.
  Its hostname regression uses an isolated marker, and CI prints failing
  tool self-test transcripts instead of hiding their assertions.
- Empty load mocks represent an unreadable instrument rather than falling
  through to the real host, keeping conservative-thread tests deterministic
  on both quiet CI runners and busy development machines.
- CI guard verification recognizes the reported comment-form self-test
  invocation, retaining its exact-once check after diagnostic integration.
- Shared CI optional-oracle admission requires completed readiness checks
  and verified output. Recognized license refusals remain optional skips;
  timeouts, malformed output, unexpected failures, and fixture mismatches
  remain hard errors.

### Validation

- CPython 3.9 differential suite: 1,642 cases, 1,494 matched, 148 recorded
  refusals, zero mismatches. The same rows through the proof interpreter:
  1,416 matched, 226 refused, zero mismatches.
- Whole-program corpus: 70 scripts, 55 matched, 15 loud refusals, zero failures.
- The two new example proof pairs are kernel-checked without
  native-computation or `sorry` dependencies and join the curated axiom gate.
- Frozen Linux quickstart: the first `tri` proof builds in 205 seconds, with
  six tutorial companions taking another 43 seconds. Timing includes fresh
  package-source clones, excludes the already-installed Lean toolchain, and
  copies no compiled artifacts; no foreign tier or Mathlib library is built.

## [0.1.2] — 2026-10-09 (tag publication pending)

### Fixed

- Native dictionary iterators and enumerations retain a resize failure on
  every later advance, even after the original size is restored. Generator
  exceptions still close their frames; the recorded `pyc-div-1` divergence
  is retired with differential regressions and a continuing alarm.
- CI installs the admitted `pyslang` major family (`>=11,<12`) for the
  existing SystemVerilog envelope gates, rather than selecting an incompatible
  newer major or weakening frontend admission.

### Changed

- The Python quickstart and tutorial proofs import only their required Python
  tactics; their targeted builds no longer compile unrelated language tiers.
  First-build commands skip the unused Mathlib cache download, and CI checks
  the examples' transitive import boundary.
- Public judgments, tactics, and existing theorem statements are unchanged.

### Added

- A dated [Python production-readiness baseline](docs/python-baseline-2026-10-09.md)
  distinguishing executable coverage, proof coverage, static refusals,
  upstream-test prerequisites, and onboarding/documentation gaps.
- Ten dictionary-iterator lifecycle regressions and five kernel-checked
  concrete theorems of the executable interpreter, preserving the narrower
  proof interpreter's loud boundary. Ten isolated tests protect the archived
  divergence alarm from being masked by the presence of a failure constructor.

### Validation

- CPython 3.9 differential suite: 1,345 cases, 1,229 matched, 116 recorded
  refusals, zero mismatches. The same rows through the proof interpreter:
  1,151 matched, 194 refused, zero mismatches.
- Both recorded Python divergences are archived and remain watched by their
  live probes. Curated existing examples and the five new concrete theorems
  retain kernel-checked proofs without native-computation or `sorry` dependencies.
- Frozen Linux quickstart: the first `tri` proof builds in 211 seconds, with
  six tutorial companions taking another 39 seconds. Timing includes fresh
  package-source clones, excludes the already-installed Lean toolchain, and
  copies no compiled artifacts; no foreign tier or Mathlib library is built.

## [0.1.1] — 2026-09-24

### Fixed

- Python harnesses re-execute under the pinned frontend only when run as
  scripts; importing them no longer forwards a caller's unrelated arguments.

### Added

- CI runs the README quickstart on Linux and macOS and checks the curated
  Python examples for `sorry` and native-computation dependencies.

### Removed

- Remaining Sunfish-derived `sf_*` examples and the C-tier twin moved out of
  this Apache-2.0 repository to the Sunfish repository.

### Validation

- After the associated corpus rows were removed, the executable suite had
  1,335 cases: 1,219 matched and 116 refused. The proof interpreter matched
  1,151 and refused 184. Both runs had zero mismatches.

## [0.1.0] — 2026-09-24

### Added

- **Pipeline.** `extractors/python/extract.py` dumps a Python file's CPython
  `ast` to a JSON envelope; `load_program` ingests it at elaboration time as a
  literal Lean term; a fuel-based definitional interpreter gives it meaning.
- **Judgments.** `f(a) ==> v` (total), `f(a) ⇓ r` (relational), `f(a) ==>! e`
  (raises), `f(a) ~~> v` (strengthened partial correctness), over `Py*`
  binders; `#py_check` for concrete runs.
- **Tactics.** `py_prove` (loop-free bodies), `py_vcgen` (loops, invariants
  and measures, `break`/`continue`/mid-loop `return`), `py_begin`/`py_loop`,
  `py_corollary`, `py_lift`, `py_threshold`, `py_simp`.
- **Semantic tier.** Arbitrary-precision ints, bools, strs, `None`, tuples,
  heap lists and dicts with aliasing, sets (order-free subset), classes
  with the narrow same-module single-base slice, namedtuples, generators and generator expressions,
  list comprehensions, nested defs and lambdas (snapshot captures),
  `try`/`except`/`raise` over a fixed set of builtin exceptions and
  user `Exception` subclasses, `%`-formatting, `print`, and a trace clock for
  `time.time()`. Anything outside the tier is refused loudly, never answered
  with a guessed value. The measured table is
  [docs/python-coverage.md](docs/python-coverage.md).
- **Differential testing.** `harness/diff_test.py` checks the semantics
  against CPython 3.9: 1419 rows, 1301 agree, 0 disagree, 118 recorded
  refusals. The theorems are about a second definition of the interpreter,
  `LeanModels/Python/Semantics.lean`. `diff_test.py --proof-interpreter`
  checks that one against the same rows: 1233 agree, 0 disagree, and 186
  refuse because its tier is narrower. CI runs both
  ([docs/python-architecture.md](docs/python-architecture.md)).
- **Whole programs.** `tools/leanpy FILE.py [--compare]` runs a Python file
  end to end under the Lean semantics and compares with CPython.
- **Coverage page.** `harness/coverage_page.py` generates
  `docs/python-coverage.md`; CI fails when it is stale.
- **Examples.** Proved examples under `Examples/python/` (three-file layout:
  `<name>.py`, `spec.lean`, `proof.lean`), including loops (`tri`, `gcd`),
  recursion (`fib`), relational specs (`rsa_inverse`), and code vendored
  from CPython (`bench_bisect`, `bench_statistics`). The remaining
  Sunfish-derived `sf_*` examples moved out of this repository in 0.1.1.
- **License.** Apache-2.0 ([LICENSE](LICENSE)); vendored third-party example
  code is listed in [NOTICE](NOTICE).
- **Docs.** Quickstart in the README, tutorials under `docs/tutorial/`, the
  judgment and tactic reference in `docs/reference.md`.

### Known limitations

- No floats, no imports beyond a small whitelist, no class inheritance, and
  most builtins refuse. See the README's limitations list and
  `docs/python-coverage.md`.
- The oracle and the tier are pinned to CPython 3.9.
- Some programs `tools/leanpy` runs cannot yet be the subject of a theorem:
  of the differential rows, the proof interpreter decides 1233 and the
  runner 1301.
- Only Linux has been timed from a fresh clone; macOS is expected to work
  but is untested.

- Python: model CPython 3.9's default recursion limit (1000) in nested calls;
  deep recursion now raises `RecursionError` instead of returning an unbounded value.
- Python: refuse script modules whose function bodies reach later definitions or
  redefine a function name; static function tables no longer silently answer
  through CPython's sequential binding.
- Python: carry `global` and `nonlocal` declarations as structured AST name
  arrays, removing the truncated text re-parser and preserving long declarations.
- Python: refuse generator-expression lowerings with unpacking or `del`
  rebinding of captured names instead of returning stale by-value captures.
- Python: perform generator-expression outer iteration at creation, matching
  CPython's `GET_ITER` timing and faithful non-iterable errors.
- Python: refuse list-comprehension lowerings when a user binding shadows the
  synthesized `list` call, avoiding a silent shadowing wrong answer.
- Python: remove the shape-specific augmented-repeat rewrite so `*=` keeps its
  in-place list semantics and public boundary list mutation remains loud.
- Python: refuse dead expression-yield assignments targeting `global` or
  `nonlocal` names instead of dropping their resumed stores.
- Python: preserve CPython's value-before-annotation order for non-simple
  annotated targets and omit annotation evaluation in function bodies.
- Python: remove `len(sequence * count)` length-only ingestion rewrites;
  oversized ordinary materialization now refuses instead of returning a
  length CPython cannot build.
- Python: refuse negative-integer set iteration, set copies, and set
  intersections until CPython's table construction and signed hashes are
  modeled soundly.
- Python: remove shape-specific builtin-alias, dead-value, immediate-genexp,
  and bare-reraise ingestion rewrites; those source shapes now retain their
  AST and refuse through the existing first-class or active-exception limits.
- Python: remove the module-level definition `del` no-op census; deleting a
  static function/class binding is now loud even when a later function body
  reaches that name.
- Python: carry value-less local annotations as structured AST nodes and remove
  the old text parser; annotation-local differential rows remain matched.
- Python: keep admitted `ImportFrom` nodes structured through ingestion and
  key benign import handling by module, names, and star fields.
- Python: carry `Try` exception-handler names as structured arrays instead of
  joining and reparsing them with a delimiter.
- Python: pin `tools/leanpy`'s frontend and comparison oracle to CPython 3.9,
  with explicit diagnostics for fallback interpreters.
- Python: retain and validate envelope frontend metadata, rejecting non-CPython
  3.9 envelopes before AST ingestion.
- Python: add differential coverage for negative set hashes and creation-time
  generator-expression iteration.
