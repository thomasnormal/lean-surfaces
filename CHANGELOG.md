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
