# PY-REAL baseline

Generated from `harness/library_corpus.json` (CPython 3.9.25, 183 modules) and the refreshed disjoint baseline chunks run on 2026-11-12. The manifest records SHA-256 hashes for all 141 pure-Python stdlib files available to the pinned interpreter.

The refreshed baseline has **12 VERIFIED public-function modules**, with 4,091 of 8,677 driven calls matching, **0 call DIVERGEs**, 8 calls that did not finish, and 41 canonical-value gaps. The run is free of decided mismatches; unfinished calls remain separately reported and are not counted as agreement. The 12 VERIFIED modules are `fstring_shadow`, `g1_lab`, `gcd`, `init_lab`, `midpoint`, `my_abs`, `nested_flow`, `sum_to`, `tut_01`, `tut_02`, `tut_03`, and `fnprint`.

The call denominator is lower than the first run because the oracle now records CPython C-accelerator overrides (`override:*`) as explicit `accelerator equivalence is unmeasured` skips. It never compares a pure-Python AST definition with a replacement C function. The four DIVERGE families from the prior refresh (`inspect.getdoc`, `arith.mod`, `gen_lab.drain_unbound`, and `str_lab.fmt_bare_leftover`) are now either matched or explicitly refused.

The observed refusal ranking is measured by both presence and `sole` census walls:

| Wall | Present | Sole |
|---|---:|---:|
| `class-creation` | 19 | 0 |
| `import` | 14 | 6 |
| `node:ImportFrom:accelerator-unmeasured` | 1 | 1 |

The remaining observed messages are four function-body definition-order walls, one heap `+` wall, one unsupported `try/except` wall, and one missing `frozenset` builtin. These are recorded per module in the JSON result and are not silently ranked as a named census wall.

The baseline command used pinned `python3.9`, fixed fuel (`100000` body, `10000` call), eight calls per public function, a 600-second body bound, and a 60-second per-module call bound. Results were merged with `library_survey.py --merge`; no module occurred in more than one chunk. The merged run is marked incomplete because eight calls did not finish within their bounds.
