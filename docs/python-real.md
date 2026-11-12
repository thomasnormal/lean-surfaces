# PY-REAL baseline

Generated from `harness/library_corpus.json` (CPython 3.9.25, 183 modules) and the refreshed disjoint baseline chunks run on 2026-11-12. The manifest records SHA-256 hashes for all 141 pure-Python stdlib files available to the pinned interpreter.

The refreshed baseline has **12 VERIFIED public-function modules**, with 4,091 of 8,677 driven calls matching, **0 call DIVERGEs**, 8 calls that did not finish, and 41 canonical-value gaps. The run is free of decided mismatches; unfinished calls remain separately reported and are not counted as agreement. The 12 VERIFIED modules are `fstring_shadow`, `g1_lab`, `gcd`, `init_lab`, `midpoint`, `my_abs`, `nested_flow`, `sum_to`, `tut_01`, `tut_02`, `tut_03`, and `fnprint`.

The call denominator is lower than the first run because the oracle now records CPython C-accelerator overrides (`override:*`) as explicit `accelerator equivalence is unmeasured` skips. It never compares a pure-Python AST definition with a replacement C function. The four DIVERGE families from the prior refresh (`inspect.getdoc`, `arith.mod`, `gen_lab.drain_unbound`, and `str_lab.fmt_bare_leftover`) are now either matched or explicitly refused.

The observed refusal ranking is measured by both presence and `sole` census walls. It was generated from the complete survey JSON with
`python3 harness/library_rank.py --provenance census:library --json /tmp/library-rank-current.json /tmp/library-current.json`.
The price columns are the measured surface in the rows that fired each wall, not a prediction that every row will flip:
modules, public functions, and driven calls.

| Wall | Present | Sole | Modules | Public functions | Driven calls |
|---|---:|---:|---:|---:|---:|
| `import` | 30 | 7 | 30 | 97 | 560 |
| `accelerator-unmeasured` | 1 | 1 | 1 | 0 | 0 |
| `node:DictComp` | 1 | 1 | 1 | 3 | 24 |
| `class-creation` | 62 | 0 | 62 | 383 | 2,015 |
| `definition-order` | 34 | 0 | 34 | 284 | 1,288 |

The remaining observed messages are one accelerator-domain wall, one heap `+` wall, one unsupported `try/except` wall, one missing `frozenset` builtin, and one list `.extend` wall. They remain recorded per module in the JSON result and are not silently omitted from the ranking.

The baseline command used pinned `python3.9`, fixed fuel (`200000` body, `10000` call), eight calls per public function, a 900-second body bound, and a 120-second per-module call bound. The complete run covered all 183 manifest and in-repo rows in one survey; its eight unfinished calls remain explicit and are not counted as agreement.
