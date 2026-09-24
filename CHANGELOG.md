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

## [0.1.0] — unreleased (first community release)

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
  from CPython (`bench_bisect`, `bench_statistics`). The sunfish chess
  engine proofs (GPL-3.0) moved to the sunfish repository before release.
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
