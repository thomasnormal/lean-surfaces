# Python production-readiness baseline — 2026-10-09

This audit starts from `e565769` on `master`, after the sunfish examples
were moved out of this repository. It inventories the shipped tier; it
does not add a construct or change a theorem. Counts below distinguish
executed checks, manifest expectations, static syntax, and actual proofs.
The frontend and differential oracle are CPython **3.9.25**. The pinned
Lean toolchain is `leanprover/lean4:v4.33.0-rc1`, with Mathlib required by
`lakefile.toml`.

## Executed validation

| Check | Result |
|---|---|
| Fresh `lake exe cache get`, then `lake build` | Passed: 8,643 cache files restored; 3,742 build jobs |
| Python runner build | Passed, 38 jobs in 84.453 seconds after shared dependencies were built |
| Function differential suite, executable interpreter | 1,335 cases: 1,219 matched, 116 recorded refusals, zero failures |
| Same suite, theorem interpreter (`--proof-interpreter`) | 1,335 cases: 1,151 matched, 184 refused, zero failures |
| Script regression corpus | 65 scripts: 50 matched, 15 loud-blocked, zero failures |
| Grammar/refusal census | 138 grammar witnesses: 107 matched, 31 refused; zero drift across grammar/function/script censuses |
| Whole-file survey | 118 files: 93 matched, 25 refused; zero divergences or other error verdicts |
| Coverage-page freshness | Passed |
| Compiled curated-example axioms | Passed: 224 declarations across 20 modules, zero native/sorry dependencies |
| Single-file warm-clone checker | Passed; the three `tri` spec axioms are only `propext`, `Classical.choice`, `Quot.sound` |
| Declared-divergence probe | Passed its guards; active `pyc-div-1` reproduced, retired `pyc-div-2` stayed retired |
| Python extractor tests | 78 passed |
| `leanpy` cache tests | 6 passed |
| Single-file checker's self-tests | 113 passed |
| Import-closure instrument self-tests | 13 passed |
| CI guard self-checks | 57 passed |
| Documentation checker | 89 marked blocks passed; 41 illustrative exemptions; 525 unmarked blocks not checked |
| Documentation checker self-tests | 5 passed |

There is no root `check.sh`. The existing `tools/check.sh` checks one
Lean file against a warm build; `.github/workflows/ci.yml` runs
`tools/ci.sh` for cross-tier CI. This audit uses the repository's Lake
commands, not the fleet's generic CMake instructions, and limits runtime
tests to the Python tier. A passing documentation check verifies marked
source quotations, not every factual claim or unmarked code block.

## Syntax and refusal inventory

All **118** corpus files were freshly extracted under CPython 3.9.25.
The wall count includes structured class-creation restrictions as well
as `Unsupported` nodes.

| Corpus group | Files | Envelope nodes | `Unsupported` nodes | Files with static walls |
|---|---:|---:|---:|---:|
| `harness/scripts/*.py` | 64 | 3,186 | 4 | 5 |
| `Examples/python/*/*.py` | 46 | 9,367 | 27 | 13 |
| Vendored CPython tests | 8 | 28,262 | 645 | 8 |
| Total | 118 | 40,815 | 676 | 26 |

The leading unsupported node kinds are float constants (176), `With`
(126), imports (99: 59 `Import`, 40 `ImportFrom`), bytes (41), sets (39),
lambdas (36), deletion (29), starred expressions (26), and true division
(23). These are node counts, not failing test counts. Unsupported nodes
hide their subtrees; static walls miss ingestion, builtin, value-dependent,
and boundary restrictions. A sole static wall does not promise that
implementing it will make the file agree with CPython.

The checked-in manifests record the following expectations, which are
not substitutes for the current runtime measurements:

| Manifest | Recorded matching | Recorded loud refusal | Total |
|---|---:|---:|---:|
| Grammar witnesses in `harness/refusal_census.py` | 107 | 31 | 138 |
| Function rows in `harness/cases.json` | 533 | 112 | 645 |
| Individual function argument cases | 1,219 | 116 | 1,335 |
| Script rows in `harness/scripts.json` | 50 | 15 | 65 |

The script manifest's extra file is
`Examples/python/import_lab/import_lab.py`, already counted in the
examples corpus. Grammar witnesses demonstrate individual uses, not
complete support for a Python grammar production.

The fresh refusal census reproduces all manifest expectations: 138
grammar witnesses (107 matches, 31 refusals), 116 unsupported function
argument cases in 47 classes, and 15 script refusals in ten classes, with
**zero drift**. Function refusal classifications are 111 interpreter
`unsupported` outcomes and five boundary-freeze refusals.

The whole-program survey gives a different denominator from function
calls; keep its definitions-only matches separate:

| Corpus group | Files | Matched | Refused | Live matches | Definitions-only matches |
|---|---:|---:|---:|---:|---:|
| Harness scripts | 64 | 49 | 15 | 49 | 0 |
| Python examples | 46 | 44 | 2 | 27 | 17 |
| Vendored upstream files | 8 | 0 | 8 | 0 | 0 |
| Total | 118 | 93 | 25 | 76 | 17 |

There are zero `DIVERGE`, `TIMEOUT`, `ORACLE`, `EXTRACT`, `HUNG`, or
`RUNNER` verdicts. Seventeen definitions-only matches exercise no function
behavior; even a live example match may execute only a docstring or module
bookkeeping. The two refusing examples are `cls_lab` (observable class
creation) and `rsa_inverse` (unsupported import). The model batch took
0.185 seconds, excluding extraction and oracle execution.

### Upstream tests are present, but not running

`vendor/cpython-3.9-lib-test/` contains eight provenance-pinned CPython
3.9.19 source files, with **342 `test_*` function definitions**, including
339 direct class methods and three nested helpers. All eight
source hashes match `PROVENANCE.md`. Executing each file under the audit's
CPython 3.9.25 exits with `ModuleNotFoundError: No module named 'test'`:
neither the vendored directory nor the installed oracle supplies
`test.support`. **Zero upstream unittest methods were demonstrated to
run.** Counting these source files as successful unittest coverage would
be incorrect.

`harness/scripts/cpython_list_basics.py` is a provenance-derived script,
with assertions replaced by output and operations omitted. It is useful
differential coverage, but not an execution of the upstream unittest
suite. All eight upstream files also have both import and class-creation
walls, so removing either wall alone would not enable that corpus.

All eight first refuse dynamically on class-creation admission. The
survey skips the oracle for model-refused files, so its zero `ORACLE`
verdict count is not an execution of these upstream tests. The separate
direct-oracle failures above establish the missing `test.support`
prerequisite.

## Proof/example inventory

The Python examples contain **46 directories, 46 Python sources, 46
envelopes, and 56 Lean files**: 36 `spec.lean`, 19 `proof.lean`, and the
generated `sum_to/SumTo.lean`.

- Twenty directories contain named theorem/lemma declarations: 19
  spec/proof pairs and the generated `sum_to` companion.
- There are 257 named declarations, counting duplicated statement/proof
  twins separately, and 794 concrete checks: 585 `#py_check`, 209 `#guard`.
- Seventeen spec-only directories are intentional checks-only batteries,
  not failed proof pairs: `alias_lab`, `closure_lab`, `cls_lab`, `dict_lab`,
  `drain_lab`, `exc_lab`, `init_lab`, `iter_lab`, `kw_lab`, `list_lab`,
  `seq_lab`, `set_lab`, `star_lab`, `star_shadow`, `str_lab`, `tut_01`,
  and `walrus_lab`.
- Nine directories have no Lean file: `ann_lab`, `assert_lab`,
  `bench_heapq_sift`, `del_lab`, `fstring_lab`, `fstring_shadow`, `g1_lab`,
  `import_lab`, and `opt_args`. `bench_heapq_sift` also has no function or
  script invocation rows; a definitions-only file match does not exercise
  its heap helpers.
- No stateful `CallsIn` theorem remains in the Python examples after the
  sunfish migration. A generic, license-compatible heap-aliasing or
  method-state proof example is missing.

Static source scans find no `sorry`, `admit`, axiom declaration, or native
decision tactic in these examples. That scan does not establish their
compiled axiom dependencies. The existing CI axiom gate covers only the
ten curated spec/proof pairs; this audit executes that gate and scans
224 declarations across their 20 modules, with zero native or `sorry`
dependencies. Other examples compile in the full build but are not part
of that curated dependency census.

The fresh differential runs reproduce **68 more refusals** for the theorem
interpreter than for the executable interpreter (184 versus 116 on the
same 1,335 calls). `Main.lean` selects different interpreters for these
two modes. Successful runner calls cannot be counted as proof coverage.

The 112 recorded unsupported function rows fall into 47 categories.
Leading buckets are exception handlers and `raise` (seven rows each),
delete-name census and set order (six each), and closure/generator-expression
admission (five each). Across all categories there are 116 individual
argument cases. The 31 recorded grammar refusals comprise 11 statement,
six dict, four expression, four constant, four operator, and two deletion
witnesses. These partitions make syntax witnesses and value-dependent
function refusals visible separately.

## Documentation and fidelity gaps

1. The targeted `tri` quickstart still imports the cross-tier `LeanModels`
   umbrella. Its static local import closure is 61 modules, including 22
   SystemVerilog, six RISC-V, and seven SoftFloat modules. The claim that
   it builds only Python is inaccurate; no fresh sub-ten-minute targeted
   quickstart timing is established by this audit.
2. `docs/tutorial/01-first-run.md` and `02-first-spec.md` prescribe bare
   `lake build`, which the README warns against. The tutorial index says
   no packages are needed despite the Mathlib dependency.
3. Python >=3.9 suffices for extraction, but differential tests target
   specifically `python3.9`. The harness warns and falls back when that
   executable is absent; `tools/leanpy --compare` defaults to `python3`.
   These are not a single pinned oracle policy.
4. `docs/python-declared-divergences.json` has one active and one retired
   divergence. Active `pyc-div-1` concerns the state of a dictionary
   iterator after a resize failure and is reproduced by its dedicated
   probe: CPython raises on another advance, while the model returns the
   supplied default. It needs separate visibility beside
   unconditional fidelity claims; zero differential-corpus mismatches
   alone does not establish absence of this recorded divergence.
5. `AGENTS.md`'s house rules still call `callFunction` a frozen recursion
   point and recommend `callFunction.eq_2`; the implementation now has a
   nonrecursive wrapper and freezes `callIn`. Another rule describes
   `Env` values as `Val`, rather than the current `RVal`.
6. Tags `v0.1.0` and `v0.1.1` exist, but the changelog still calls 0.1.0
   unreleased and has no 0.1.1 entry. Contributing still names 0.1.0.
7. Current memory-model and generator-architecture documentation retains
   16 path-reference lines to removed sunfish examples. The operating
   manual references eight distinct missing paths. The examples README
   correctly explains the migration; references should point to the
   external package, not restore GPL sources.

## First-user order

1. **Onboarding/build boundary:** make the first Python proof use
   Python-only imports, make tutorial commands targeted, and measure the
   cold quickstart rather than promise a timing from a broader build.
2. **Fidelity visibility and regression:** resolve the now-reproduced
   active dict-iterator divergence before broadening fidelity claims.
3. **A bounded ordinary construct:** extend decimal-string parsing;
   basic `int(str)` already works. One refusal row carries three cases:
   `"1_2"`, `"12x3"`, and `"٣"` (CPython returns 12, raises `ValueError`,
   and returns 3 respectively). Price larger float/true-division support
   separately rather than bundling it with integer parsing.
4. **Invalid-input contracts:** normal `raise`, handler ancestry,
   `finally`, and exception construction; then collection boundary/API
   consistency and a real stateful proof example.
5. **Function/text syntax:** remaining keyword/starred-call, annotation,
   closure/nonlocal, and f-string/percent-format restrictions.
6. **Credible upstream validation:** provide the support/discovery
   prerequisites for the vendored subset, then price imports, classes,
   and context managers by actual additional executed tests. Do not
   equate static wall frequency with the payoff of a semantic tier.

## Reproduction

From the repository root, after fetching the pinned dependencies:

```sh
lake exe cache get
lake build
python3.9 harness/diff_test.py --no-build --runner .lake/build/bin/leanmodels-run
python3.9 harness/diff_test.py --no-build --runner .lake/build/bin/leanmodels-run --proof-interpreter
python3.9 harness/script_corpus.py --no-build --runner .lake/build/bin/leanmodels-run
python3.9 harness/refusal_census.py --no-build --runner .lake/build/bin/leanmodels-run
python3.9 harness/leanpy_survey.py --corpus harness/leanpy_corpus.json
python3.9 harness/coverage_page.py --check
python3 extractors/python/test_extract.py
python3 tools/test_leanpy.py
python3.9 harness/import_closure.py --self-test
bash tools/check.sh --self-test
bash tools/ci.sh --verify-guards
python3 tools/docs_check.py
```

The refusal census's JSON export covers grammar rows only; retain stdout
for its function/script classifications. Preserve both runner and theorem
interpreter summaries. Record unavailable or refused checks as such,
never as passing coverage.
