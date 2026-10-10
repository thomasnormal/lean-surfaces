# Changelog

All notable changes to the **Python tier** of this repository (the extractor,
the Lean semantics under `LeanModels/Python/`, its proof surface, and its
tools). The other tiers (SystemVerilog, C++, RISC-V) are versioned separately
and are not covered here.

The public surface these entries track is listed in
[docs/reference.md § Public surface and stability](docs/reference.md#public-surface-and-stability-0x).
While the version is 0.x, a minor release may change that surface; every such
change is listed here under **Changed** or **Removed**.

## [Unreleased]

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

### Fixed

- The refusal census classifies all recorded closed-function and script gaps,
  including the recent parsing, repetition, rendering, and exception fixtures.
  CI now runs both inventories and checks regressions for missing classifications
  and model answers to deliberately loud rows; no interpreter behavior or
  differential expectation changes.

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
  without inheritance, namedtuples, generators and generator expressions,
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
