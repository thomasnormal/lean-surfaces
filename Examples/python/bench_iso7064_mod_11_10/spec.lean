/-
Examples/python/bench_iso7064_mod_11_10 — checks-only spec (no proof.lean;
cf. Examples/python/tut_01/spec.lean for the checks-only precedent):
bench_iso7064_mod_11_10.py (vendored BYTE-VERBATIM from python-stdnum 2.2
`stdnum/iso7064/mod_11_10.py` — provenance in its module docstring),
bench_iso7064_mod_11_10.json (generated envelope), THIS FILE (the
interpreter-status census rows).

BENCHMARK STATUS (Band B, docs/benchmark.md rows 5-8): all four functions
are BLOCKED at the current tier — `checksum` by {For, call:int},
`calc_check_digit` by {call:str, callee `checksum`}, `validate`/`is_valid`
by {Try, …}. A cold-prover run (2026-07-30, docs/benchmark.md
"Cold-prover runs") verified this classification against the INTERPRETER
(not just the envelope — surprise #2 of the vendoring log), proved the
blockage as kernel-checked theorems in its scratch deliverable, and
differentially validated a line-by-line Lean model of the algorithm on
120 CPython ground-truth rows; its stuck-point analysis is quoted
verbatim in docs/benchmark.md. What lands in-tree is this census block:
the loud-refusal rows below are the machine-checked record of WHERE the
tier boundary cuts these functions, and will flip to real specs when
{For-over-str, call:int/str/bool, Try} land.

House style: `unsupported`-outcome checks stay raw `#guard … matches`
(no surface form — deliberate); the two `raises` rows are real `.exn`
outcomes of the v0 semantics and use `#py_check`.

Non-vacuity gap (recorded per AGENTS.md): no `harness/cases.json` rows —
`leanmodels-run` parses CLI args as ints only and these functions take
digit STRINGS. The CPython ground truth for the rows below:
`checksum('794623') == 1` (valid number), `checksum('') == 5`,
`validate('794623') == '794623'`, `is_valid('794623') is True`,
`calc_check_digit('79462') == '3'`.
-/
import LeanModels

open LeanModels LeanModels.Python

load_program bench_iso7064_mod_11_10 from "Examples/python/bench_iso7064_mod_11_10/bench_iso7064_mod_11_10.json"

/-! ## Interpreter-status census (the tier boundary, kernel-checked)

`checksum` reaches its `for` statement (after `check = 5`) and is refused
loudly; `validate`/`is_valid` are gated by the `try` wrapping their NORMAL
path (the benchmark's row-7 note: the unreachable `raise` inside needs no
tier growth, but `Try` gates the happy path). -/
#guard callFunction bench_iso7064_mod_11_10 "checksum" #[.str "794623"] 4096 matches .unsupported _
#guard callFunction bench_iso7064_mod_11_10 "checksum" #[.str ""] 4096 matches .unsupported _
#guard callFunction bench_iso7064_mod_11_10 "validate" #[.str "794623"] 4096 matches .unsupported _
#guard callFunction bench_iso7064_mod_11_10 "is_valid" #[.str "794623"] 4096 matches .unsupported _
#guard callFunction bench_iso7064_mod_11_10 "checksum" #[.str "794623"] 4 matches .timeout

/-! ## Pinned fidelity artifact (cold-prover finding, framework fix
indicated — docs/benchmark.md): `calc_check_digit`'s body is one
`str(...)` of in-tier arithmetic, and `str` hits the v0 name-resolution
rule (local env → module functions → builtin `len` → NameError), so the
v0 semantics RAISES `NameError("str")` where CPython returns `'3'` — a
refusal that is loud in outcome but wrong in KIND (`.exn`, not
`.unsupported`). Recorded here so the gap stays visible until the
name-resolution fix lands; this row must flip to a real spec (or to
`.unsupported`) — never be deleted. -/
#py_check bench_iso7064_mod_11_10.calc_check_digit("79462") raises (.nameError "str")

/-! The one positive arrow the tier admits today, faithful in exception
CLASS to CPython: wrong arity errs like the real thing (the in-tier
prefix of the call protocol works). -/
#py_check bench_iso7064_mod_11_10.checksum() raises
  (.typeError "checksum() takes 1 positional arguments but 0 were given")
