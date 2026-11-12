# PY-REAL baseline

Generated from `harness/library_corpus.json` (CPython 3.9.25, 183 modules) and the refreshed disjoint baseline chunks run on 2026-11-12. The manifest records SHA-256 hashes for all 141 pure-Python stdlib files available to the pinned interpreter.

The refreshed baseline has **12 VERIFIED public-function modules**, with 4,091 of 8,677 driven calls matching, **0 call DIVERGEs**, 8 calls that did not finish, and 41 canonical-value gaps. The run is free of decided mismatches; unfinished calls remain separately reported and are not counted as agreement. The 12 VERIFIED modules are `fstring_shadow`, `g1_lab`, `gcd`, `init_lab`, `midpoint`, `my_abs`, `nested_flow`, `sum_to`, `tut_01`, `tut_02`, `tut_03`, and `fnprint`.

The function-level scoreboard has **21 VERIFIED functions out of 540 modeled public functions**, with 503 matching calls among the function calls driven by this survey. A function is counted when at least one pinned CPython call returns normally and every driven call for that function matches; C-accelerator and unsafe-call entries are explicit skips and are outside the modeled-function denominator. A module-level refusal does not turn an independently matching function back into a potential flip. The current top wall prices **3 potential function flips**, all in the import wall.

The call denominator is lower than the first run because the oracle now records CPython C-accelerator overrides (`override:*`) as explicit `accelerator equivalence is unmeasured` skips. It never compares a pure-Python AST definition with a replacement C function. The four DIVERGE families from the prior refresh (`inspect.getdoc`, `arith.mod`, `gen_lab.drain_unbound`, and `str_lab.fmt_bare_leftover`) are now either matched or explicitly refused.

The observed refusal ranking is measured by function flips first, then newly agreed calls, with `sole` and `present` retained as context. It was generated from the complete survey JSON with
`python3 harness/library_rank.py --provenance census:library --json /tmp/library-rank-current.json /tmp/library-current.json`.
The price columns are measured surfaces, not promises: modules, public functions, driven calls, matched calls, rows that would become verified, and functions that would become verified if that wall alone were removed.

| Wall | Present | Sole | Modules | Public functions | Driven calls | Matched calls | Potential rows | Function flips |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `import` | 30 | 7 | 30 | 77 | 560 | 142 | 1 | 3 |
| `class-creation` | 62 | 0 | 62 | 282 | 2,015 | 183 | 1 | 6 |
| `definition-order` | 34 | 0 | 34 | 178 | 1,288 | 162 | 0 | 6 |
| `node:DictComp` | 1 | 1 | 1 | 3 | 24 | 16 | 0 | 1 |
| `accelerator-unmeasured` | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |

The remaining import potential set is `{email.charset.add_alias, email.charset.add_charset, email.charset.add_codec}`. The measured opaque arm now binds allowlisted modules and leaves independently matching functions counted as VERIFIED; `rsa_inverse` remains a separate annotation-observation check.

The remaining observed messages are one accelerator-domain wall, one heap `+` wall, one unsupported `try/except` wall, one missing `frozenset` builtin, and one list `.extend` wall. They remain recorded per module in the JSON result and are not silently omitted from the ranking.

The baseline command used pinned `python3.9`, fixed fuel (`200000` body, `10000` call), eight calls per public function, a 900-second body bound, and a 120-second per-module call bound. The complete run covered all 183 manifest and in-repo rows in one survey; its eight unfinished calls remain explicit and are not counted as agreement.
