# PY-REAL baseline

Generated from `harness/library_corpus.json` (CPython 3.9.25, 183 modules) and the disjoint baseline chunks run on 2026-11-12. The manifest records SHA-256 hashes for all 141 pure-Python stdlib files available to the pinned interpreter.

The first baseline is **12 VERIFIED public-function modules**, with 4,439 of 9,341 driven calls matching, 53 call DIVERGEs, 7 calls that did not run, and 43 canonical-value gaps. The baseline is not a green PY-REAL result: DIVERGE rows remain and are the next priority. The 12 VERIFIED modules are `fstring_shadow`, `g1_lab`, `gcd`, `init_lab`, `midpoint`, `my_abs`, `nested_flow`, `sum_to`, `tut_01`, `tut_02`, `tut_03`, and `fnprint`.

The observed refusal ranking is measured by both presence and `sole` census walls:

| Wall | Present | Sole |
|---|---:|---:|
| `class-creation` | 19 | 0 |
| `import` | 14 | 6 |
| `node:ImportFrom:accelerator-unmeasured` | 1 | 1 |

The remaining observed messages are four function-body definition-order walls, one heap `+` wall, one unsupported `try/except` wall, and one missing `frozenset` builtin. These are recorded per module in the JSON result and are not silently ranked as a named census wall.

The baseline command used pinned `python3.9`, fixed fuel (`100000` body, `10000` call), eight calls per public function, a 600-second body bound, and a 60-second per-module call bound. Results were merged with `library_survey.py --merge`; no module occurred in more than one chunk.
