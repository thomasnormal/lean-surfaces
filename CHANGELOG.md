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

- The `round()` builtin now models its one-argument integer and Boolean slice,
  including CPython's exact missing-number `TypeError`; float rounding and
  `ndigits` remain loud until their oracle is specified. The CPython 3.9
  differential suite now has **2,760 / 3,086 rows = 89.4% complete** natively
  and **2,686 / 3,086 = 87.0% complete** in the proof interpreter, with **100%
  agreement among decided rows** and zero failures.

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
