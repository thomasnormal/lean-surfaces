# PY-REAL baseline

Generated from `harness/library_corpus.json` (CPython 3.9.25, 183 modules) and the refreshed disjoint baseline chunks run on 2026-11-12. The manifest records SHA-256 hashes for all 141 pure-Python stdlib files available to the pinned interpreter.

The full post-stall survey (141 pinned CPython 3.9.25 library rows, run 2026-11-12) has **13 VERIFIED public-function modules**, with 4,091 of 8,677 driven calls matching, **0 call DIVERGEs**, 8 calls that did not finish, and 41 canonical-value gaps. The targeted import refresh flipped `email.charset` from body REFUSED to VERIFIED with 24/24 matching calls; the call denominator is unchanged because those calls were already driven through the closed-function surface. The 13 VERIFIED modules are `email.charset`, `fstring_shadow`, `g1_lab`, `gcd`, `init_lab`, `midpoint`, `my_abs`, `nested_flow`, `sum_to`, `tut_01`, `tut_02`, `tut_03`, and `fnprint`.

The function-level scoreboard has **21 VERIFIED functions out of 540 modeled public functions**, with 503 matching calls among the function calls driven by this survey. A function is counted when at least one pinned CPython call returns normally and every driven call for that function matches; C-accelerator and unsafe-call entries are explicit skips and are outside the modeled-function denominator. A module-level refusal does not turn an independently matching function back into a potential flip. After the targeted import refresh, no remaining wall has a measured function flip; the next price is by newly agreed calls and module rows.

The call denominator is lower than the first run because the oracle now records CPython C-accelerator overrides (`override:*`) as explicit `accelerator equivalence is unmeasured` skips. It never compares a pure-Python AST definition with a replacement C function. The four DIVERGE families from the prior refresh (`inspect.getdoc`, `arith.mod`, `gen_lab.drain_unbound`, and `str_lab.fmt_bare_leftover`) are now either matched or explicitly refused.

The observed refusal ranking is measured by function flips first, then newly agreed calls, with `sole` and `present` retained as context. The required stall-rule rerun used the complete 141-row survey JSON on 2026-11-12 with
`python3 harness/library_rank.py --provenance census:library --json /tmp/library-rank-current.json /tmp/library-current.json`.
The price columns are measured surfaces, not promises: modules, public functions, driven calls, matched calls, rows that would become verified, and functions that would become verified if that wall alone were removed.

| Wall | Present | Sole | Modules | Public functions | Driven calls | Matched calls | Potential rows | Function flips |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `class-creation` | 62 | 0 | 62 | 282 | 2,015 | 183 | 1 | 0 |
| `definition-order` | 34 | 0 | 34 | 178 | 1,288 | 162 | 0 | 0 |
| `import` | 29 | 6 | 29 | 74 | 536 | 118 | 0 | 0 |
| `node:DictComp` | 1 | 1 | 1 | 3 | 24 | 16 | 0 | 0 |
| `accelerator-unmeasured` | 1 | 1 | 1 | 0 | 0 | 0 | 0 | 0 |
| `accelerator-outside-domain` | 2 | 0 | 2 | 0 | 0 | 0 | 0 | 0 |
| `frozenset` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| `heap-plus` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| `method call '.extend' on a list is outside the tier` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| `try-except` | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 0 |

The measured opaque arm now admits the imports needed by `email.charset`; its three public functions are body- and call-verified. `rsa_inverse` remains a separate annotation-observation check. The next ranked wall remains `class-creation`, priced by its 183 newly matching calls and one potential whole-row verification; it has **0 function flips**. The three-item stall rule therefore requires a replan before another zero-flip semantic tier.

The remaining observed messages are one accelerator-domain wall, one heap `+` wall, one unsupported `try/except` wall, one missing `frozenset` builtin, and one list `.extend` wall. They remain recorded per module in the JSON result and are not silently omitted from the ranking.

The baseline command used pinned `python3.9`, fixed fuel (`200000` body, `10000` call), eight calls per public function, a 900-second body bound, and a 120-second per-module call bound. The complete run covered all 183 manifest and in-repo rows in one survey; its eight unfinished calls remain explicit and are not counted as agreement.
