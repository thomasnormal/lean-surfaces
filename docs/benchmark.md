# Python benchmark — real-world target scoreboard (v1)

A fixed suite of real, important Python functions (CPython stdlib + PyPI),
vendored **byte-verbatim** under `Examples/python/bench_*/`, whose
proved/blocked status is tracked here. The suite is the measuring stick for
tier growth: a status only flips to `provable-now` when the tier actually
supports every construct the function executes, and only flips to **proved**
when a `proof.lean` with no `sorry`/`admit`/`native_decide`/axioms lands.

Ground rules (inherited from `docs/DESIGN.md` and the rsa_inverse precedent):

- **Vendoring**: function bodies are byte-verbatim copies of the original
  source, with line ranges and per-segment sha256 recorded in each file's
  module docstring. Names that occur *only* inside `raise` statements or
  `except` clauses (exception classes) are not vendored — the rsa_inverse
  rule: no valid-input run evaluates them.
- **Envelopes**: every vendored source has its envelope
  (`bench_x/bench_x.json`) extracted by `extractors/python/extract.py`.
  Since the F1 sprint, LITERAL defaults (int/bool/str/None) ride on the
  params as `"default"` payloads and are in tier; only NON-literal defaults
  (easter's `method=EASTER_WESTERN`) still show
  `args_unsupported: "defaults"` — that is expected and *is* the data.
- **Unreached ≠ supported-needed**: the interpreter refuses an `Unsupported`
  statement only when execution reaches it (`execStmt`, Semantics.lean).
  A `raise` guard behind a false condition needs *no* tier growth — only a
  hypothesis in the theorem (rsa_inverse's `NotRelativePrimeError` argument).
- Re-extraction check (2026-07-29, HEAD 12b222a+): all 17 pre-existing
  `Examples/python/*` sources re-extracted; every existing envelope
  byte-identical.
- Re-extraction check (2026-07-30, F1/F2 sprint): all sources re-extracted
  with the defaults-emitting extractor; all 17 pre-existing envelopes again
  byte-identical (no existing example uses defaults or `is`); the 12
  `bench_*` envelopes changed as expected (literal defaults now on params,
  `is None` now an in-tier `Compare`), and are byte-stable under double
  extraction.

## Flagships vs. census rows

The suite plays two different roles, and rows are labeled by which one they
serve (curation rule set 2026-07-31):

- **Flagships** are the functions whose *proofs are interesting* — the
  correctness argument needs an invariant or induction that is not visible in
  the code text (binary-search bounds, the heap property). These carry the
  narrative and are what we showcase. Current flagships: **`rsa_inverse`**
  (proved — `Examples/python/rsa_inverse`, the pre-benchmark precedent:
  python-rsa's extended-Euclid modular inverse, Bézout invariant),
  **`bisect`** (proved), **`heapq._siftdown`/`_siftup`** (next; drives the
  mutation tier), and **`statistics`** (interesting, **proof missing** — the
  medians are one tier feature away, see the flagship plan below).
- **Census rows** are tier instrumentation: formula- and fold-shaped
  functions (checksums, calendar math, string munging, date formulas) whose
  specs are nearly definitional. They are cheap, dense probes that price tier
  features — the blocker histogram and unlock projections below are their
  product — but they are *not* individual showcases, and redundant family
  variants (the three ISO 7064 files) are counted as one idiom, not three
  results. New vendoring follows the same rule: no more checksum-class
  targets as headline items; candidates must have flagship-grade invariant
  content (e.g. `fractions.limit_denominator` best-rational-approximation,
  pure-Python `isqrt`, `date.toordinal`/`fromordinal` as a proved bijection).

## Bands

- **Band A — flagship**: CPython `bisect`. Smallest tier step, biggest name.
- **Band B — pure-int / near-tier**: checksum arithmetic and calendar math
  whose cores are Presburger-flavored integer folds. Census rows.
- **Band C — frontier markers**: one representative per hard feature class
  (float results, in-place mutation, slices/comprehensions, str-method-heavy
  code). These measure what v0 *honestly cannot* do; some are vendored,
  heavy ones are census references only. Contains one flagship: the heapq
  sift pair.

## Scoreboard

Origin shas abbreviated to 12 hex chars; full sha256 (file, sdist, and
per-segment) are in each vendored file's docstring. Status is against the
tier at HEAD (nothing beyond DESIGN.md v0). "callee X" means the function's
own body adds no new blocker but it calls blocked same-file function X.

| # | Target (vendored dir / function) | Origin + version + sha | Band | Status | Candidate spec (honest) | Notes |
|---|---|---|---|---|---|---|
| 1 | bench_bisect / `bisect_left` | CPython 3.9.25 bisect.py `6f213241b0d2` | A | **PROVED** (2026-07-30, cold-prover run; `Examples/python/bench_bisect/spec.lean`: `bisect_left_terminates` — unconditional, no sortedness — `bisect_left_sorted`, `bisect_left_insertion_point`, `bisect_left_partial`) | sorted int list `a`, `lo=0`: returns least `i ≤ len a` with `∀ j < i, a[j] < x` and `∀ j ≥ i, x ≤ a[j]` — proved as stated, plus the deterministic value `(a.takeWhile (· < x)).length` | 3.9 signature `(a,x,lo=0,hi=None)`: NO keyword-only `key` (3.10+), no slicing. Both defaults engaged; the unreachable `Raise` guard discharged by `lo = 0` (rsa_inverse precedent). |
| 2 | bench_bisect / `bisect_right` | CPython 3.9.25 bisect.py `6f213241b0d2` | A | **PROVED** (as row 1; `bisect_right_terminates`, `bisect_right_total`, `bisect_right_sorted`, `bisect_right_insertion_point`, `bisect_right_partial`) | same with `a[j] ≤ x` / `x < a[j]` — proved, plus the deterministic value `(a.takeWhile (· ≤ x)).length` | Identical shape to bisect_left. |
| 3 | bench_calendar / `isleap` | CPython 3.9.25 calendar.py `3ef1adcb836f` | B | **PROVED** (2026-07-30, cold-prover run; `Examples/python/bench_calendar/spec.lean`: `isleap_spec`) | `isleap y = (y%4=0 ∧ (y%100≠0 ∨ y%400=0))` — proved as stated (`Int.fmod`) | Zero blockers. First real-stdlib function proved. |
| 4 | bench_calendar / `leapdays` | CPython 3.9.25 calendar.py `3ef1adcb836f` | B | **PROVED** (as row 3; `leapdays_arith` + `leapdays_count`) | for `y1 ≤ y2`: equals `#{y ∈ [y1,y2) | isleap y}` (closed-form-vs-count lemma is Lean-side arithmetic) — proved EXACTLY so: closed form AND the per-year reference count `leapCount` | Zero blockers. AugAssign Sub + FloorDiv only. |
| 5 | bench_iso7064_mod_11_10 / `checksum` | python-stdnum 2.2 iso7064/mod_11_10.py `9b87a6c1b1a2` | B | blocked-by {For, call:int} | fold invariant `0 ≤ check ≤ 9`; number valid ⟺ checksum = 1 | For over a str param; `int(n)` on 1-char digit strs; `check or 10` already in-tier. |
| 6 | bench_iso7064_mod_11_10 / `calc_check_digit` | same | B | blocked-by {call:str, callee `checksum`} | `checksum(number + calc_check_digit(number)) = 1` (roundtrip) | Body is one `str(...)` of in-tier arithmetic. |
| 7 | bench_iso7064_mod_11_10 / `validate` | same | B | blocked-by {Try, Raise, callee `checksum`} | on valid input returns its argument unchanged | `raise` paths unreachable for valid inputs, but Try wraps the *normal* path — Try support required. |
| 8 | bench_iso7064_mod_11_10 / `is_valid` | same | B | blocked-by {Try, call:bool, callee `validate`} | `is_valid n = (checksum n = 1)` for nonempty digit strs | The stdnum 4-function idiom, instance 1 of 3. |
| 9 | bench_iso7064_mod_11_2 / `checksum` | python-stdnum 2.2 iso7064/mod_11_2.py `e23a4687a284` | B | blocked-by {For, IfExp, call:int} | fold `check = (2·check + digit) mod 11`; valid ⟺ 1; ISBN-10/ISNI algebra | `10 if n == 'X' else n` adds IfExp vs mod_11_10. |
| 10 | bench_iso7064_mod_11_2 / `calc_check_digit` | same | B | blocked-by {IfExp, call:str, callee `checksum`} | `checksum(number + digit) = 1`, digit ∈ 0-9,X | `'X' if c == 10 else str(c)`. |
| 11 | bench_iso7064_mod_11_2 / `validate` | same | B | blocked-by {Try, Raise, callee `checksum`} | as row 7 | Byte-identical segment to row 7 (same sha256 `f4b7e2300022…`). |
| 12 | bench_iso7064_mod_11_2 / `is_valid` | same | B | blocked-by {Try, call:bool, callee `validate`} | as row 8 | Byte-identical segment to row 8. |
| 13 | bench_iso7064_mod_97_10 / `_to_base10` | python-stdnum 2.2 iso7064/mod_97_10.py `ffd72642a9e1` | B | blocked-by {Attribute `''.join`, GeneratorExp; hidden inside genexp: call:str, **2-arg** `int(x, 36)`} | maps each base-36 char to its decimal digits, concatenated | The IBAN letter→digits step. 2-positional-arg builtin call is a distinct tier feature. |
| 14 | bench_iso7064_mod_97_10 / `checksum` | same | B | blocked-by {call:int (str→int), callee `_to_base10`} | IBAN validity ⟺ `int(_to_base10 n) mod 97 = 1` | Body itself is one int() + `% 97`. |
| 15 | bench_iso7064_mod_97_10 / `calc_check_digits` | same | B | blocked-by {**str-%-formatting** (`'%02d' % …`), callee `checksum`} | `validate(number + digits)` succeeds | **Census-invisible blocker**: `%` on a str parses as in-tier `BinOp:Mod`; the interpreter refuses it loudly at runtime (Semantics.lean "'%' string formatting"). Syntax-level censuses under-count this. |
| 16 | bench_iso7064_mod_97_10 / `validate` | same | B | blocked-by {Try, Raise, callee `checksum`} | as row 7 | Byte-identical segment to row 7. |
| 17 | bench_iso7064_mod_97_10 / `is_valid` | same | B | blocked-by {Try, call:bool, callee `validate`} | as row 8 | Byte-identical segment to row 8. |
| 18 | bench_stdnum_luhn / `checksum` | python-stdnum 2.2 luhn.py `ac87edae3e77` | B | blocked-by {Subscript:Slice `[::2]`/`[1::2]`, GeneratorExp, call:sum/tuple; hidden in genexp: Attribute `.index`, call:reversed/str} — defaults cleared by F1 | Luhn-mod-N sum ≡ 0; classic credit-card check | Luhn mod N generalization: `alphabet: str = '0123456789'` (a literal str default, now in tier). |
| 19 | bench_stdnum_luhn / `validate` | same | B | blocked-by {Try, Raise, call:bool, callee `checksum`} — defaults cleared by F1 | valid input returned unchanged | |
| 20 | bench_stdnum_luhn / `is_valid` | same | B | blocked-by {Try, call:bool, callee `validate`} — defaults cleared by F1 | `is_valid n ⟺ checksum n = 0` | |
| 21 | bench_stdnum_luhn / `calc_check_digit` | same | B | blocked-by {call:str, callee `checksum`; negative index in-tier} — defaults cleared by F1 | `checksum(n + digit) = 0` roundtrip | `alphabet[-ck]` negative indexing is already in-tier. |
| 22 | bench_dni_check / `calc_check_digit` | python-stdnum 2.2 es/dni.py `d1fc9a757a54` | B | blocked-by {call:int (str→int)} — **single blocker** | returns `'TRWAGMYFPDXBNJZSQVHLCKE'[int(n) % 23]`; output is one of 23 letters | Nearest-to-tier real PyPI function found by the census. String subscript already in-tier. |
| 23 | bench_easter / `easter` | python-dateutil 2.9.0.post0 easter.py `772062fa52af` | B (aspirational) | blocked-by {**non-literal** default (`method=EASTER_WESTERN`, a Name), Raise (reachable only for method∉1..3), Attribute `datetime.date`, call:int} | for 1583 ≤ y, method 3: returns Gregorian Easter; provable targets: month ∈ {3,4,5}, day ∈ 1..31 | The ~25-line Gauss computus core is 100% in-tier; blocked by its shell. Confirmed post-F1: still `args_unsupported: "defaults"` (Name defaults stay out, by the literals-only rule). |
| 24 | bench_luhn / `checksum` | PyPI luhn 0.2.0 luhn.py `c6e9aadd7361` | C | blocked-by {Subscript:Slice **negative-step** `[-1::-2]`/`[-2::-2]`, ListComp, call:list/map/sum; hidden: `int` referenced as a *value* (map arg), call:divmod} | digit-sum-with-doubling ≡ 0 mod 10 | Slice/comprehension marker. Function-as-value (`map(int, …)`) is its own tier feature. |
| 25 | bench_luhn / `verify` | same | C | blocked-by {callee `checksum`} — own body in-tier | `verify s ⟺ checksum s = 0` | |
| 26 | bench_luhn / `generate` | same | C | blocked-by {callee `checksum`} — own body in-tier (str concat is in-tier) | `verify(s + str(generate s))` | |
| 27 | bench_luhn / `append` | same | C | blocked-by {call:str, callee `generate`} | as row 26, packaged | |
| 28 | bench_statistics / `median` | CPython 3.9.25 statistics.py `8dd0406ee898` | C | blocked-by {call:sorted, Raise (empty input), **BinOp:Div → float** on even length} | odd n: middle element of sorted data | **Float marker**: `(a+b)/2` is a float — out of `Val` entirely; even-length median is out of scope for v0, not "one feature away". |
| 29 | bench_statistics / `median_low` | same | C | blocked-by {call:sorted, Raise} | `sorted(data)[(n-1)//2]` for nonempty data | Pure once sorted() exists (or on pre-sorted input). |
| 30 | bench_statistics / `median_high` | same | C | blocked-by {call:sorted, Raise} | `sorted(data)[n//2]` for nonempty data | |
| 31 | bench_heapq_sift / `_siftdown` | CPython 3.9.25 heapq.py `0351667ed3af` | C | blocked-by {Subscript-store, BinOp:RShift, **caller-visible mutation** (aliasing)} | restores heap invariant on `heap[startpos..pos]`, permutation of input | **Mutation marker**: value semantics cannot show the caller the in-place writes; needs a state-threading transform (return the list), which breaks byte-verbatim calling convention. |
| 32 | bench_heapq_sift / `_siftup` | same | C | blocked-by {Subscript-store, caller-visible mutation, callee `_siftdown`} | as row 31 from a leaf push | These two are the real runtime code: the C accelerator does not replace underscore helpers. |
| 33 | bench_capwords / `capwords` | CPython 3.9.25 string.py `bc57c407a839` | C | blocked-by {Attribute `.join`, GeneratorExp; hidden in genexp: `.capitalize`, `.split`} — defaults cleared by F1 | `capwords(s) = ' '.join(w.capitalize() for w in s.split())` | **String-heavy marker**: str methods are the gate (census: Attribute = 739/1591 real functions). |

### Census references (NOT vendored — status tracked, bodies stay upstream)

| Target | Origin | Why reference-only | Blockers |
|---|---|---|---|
| `statistics.mean` | CPython 3.9.25 statistics.py `8dd0406ee898` | drags in `_sum`/`_convert`/`Fraction` machinery (100+ lines, heavy) | import-call {iter, list, _sum, _convert}, Assert, tuple-unpack of call result, Attribute, true division → float |
| `bisect.insort_left` / `insort_right` | CPython 3.9.25 bisect.py `6f213241b0d2` | 2-line bodies, but the point is `a.insert(lo, x)` — method-call mutation | Attribute call + caller-visible mutation, defaults |
| `stdnum.verhoeff.checksum` / `stdnum.damm.checksum` | python-stdnum 2.2 | reference **module-level table constants** — v0 `callFunction` has no globals, so vendoring them cannot run | module-globals (a blocker class no syntax census row shows), For, enumerate/reversed genexp, nested subscripts |
| stdnum `compact`/`format` idiom (e.g. `es.dni.compact`) | python-stdnum 2.2 | 203 `compact` + 94 `format` functions gated on `stdnum.util.clean`/`isdigits` (regex) | Attribute str/re methods, import-call |

## Scoreboard summary (HEAD, 2026-07-30 — post F1/F2 sprint + cold-prover landing)

- Vendored: **33 functions / 12 suites**. **Proved: 4** (bisect_left,
  bisect_right, isleap, leapdays — every function the tier classified
  provable-now IS now proved, all four by cold prover agents working from
  the repo docs alone; see "Cold-prover runs" below). Blocked: 29.
- Flagship view: **2 of 4 flagships proved** (rsa_inverse — outside this
  suite's numbering — and bisect; heapq sift and statistics still blocked —
  those two are the scoreboard's real frontier). isleap/leapdays are census
  wins: they price tier features, they are not showcases.
- Landed proof artifacts: `Examples/python/bench_bisect/{spec,proof}.lean`
  (9 theorems), `Examples/python/bench_calendar/{spec,proof}.lean`
  (3 program theorems + the counting lemma), and the checks-only census
  spec `Examples/python/bench_iso7064_mod_11_10/spec.lean` (blocked
  target — loud-refusal rows, kernel-checked). Axiom audit: every landed
  theorem depends on exactly `[propext, Classical.choice, Quot.sound]`.
  No `sorry`/`admit`/`native_decide` anywhere.
- **Unlock delta of the F1/F2 sprint: 2 → 4 provable-now** (the two Band-A
  flagships), exactly the pre-sprint projection. Five more functions shed a
  blocker without flipping (rows 18–21 and 33 lost `defaults`); rows 1–2
  lost both `defaults` and `is-None`; no other row carried F1/F2 blockers
  (easter's is non-literal and correctly stays).
- Flagship non-vacuity (interpreter-checked, not just census: surprise #2
  below says the envelope can lie): the vendored `bisect_left`/`bisect_right`
  run from their envelope agree with CPython 3.9.25 on sorted-list probes at
  arities 2 (both defaults filled — the `hi is None` branch), 3, and 4;
  `lo < 0` is the sole path reaching the residual `Unsupported Raise`
  (CPython: `ValueError`, Lean: loud `unsupported`), confirming the
  proof-side `lo ≥ 0` classification.
- Blocker histogram over the 33 (census with gateway re-entry; a function
  counts once per blocker), post-F1/F2: Raise 10 · Try 8 · import-call 15
  (int 5, bool 5, str 3, sorted 3, sum 2, tuple/list/map 1 each) ·
  Attribute 3 · GeneratorExp 3 · For 2 · IfExp 2 ·
  Subscript:Slice 2 · Subscript-store 2 · callee-only 3 ·
  BinOp:{Div,RShift} 1+1 · ListComp 1 · str-%-format 1 (census-invisible) ·
  non-literal default 1 (easter) · caller-visible mutation 2.
  (Pre-sprint the histogram additionally had: defaults 8 · Compare:Is 2 —
  both classes now empty; the literal-defaults 8 cleared by F1, the
  non-literal 1 correctly stays.)
- Projection (fixed-point, same census): tier + {For-over-str, call:int,
  call:str, IfExp} → **9/33** (adds rows 5, 6, 9, 10, 22). Further
  + {Try, Raise, call:bool} → **13/33** (adds rows 7, 8, 11, 12).

## Flagship plan: `bisect_left` / `bisect_right`

Claim under test: *"bisect needs {defaults, is-None} only."* — **settled
2026-07-30: the F1/F2 sprint landed both features and the claim held.**
Post-sprint census of the re-extracted `bench_bisect.json`: both functions
have `args_unsupported: null`, `lo`/`hi` carry `default` payloads
(`{"type":"int","repr":"0"}` / `{"type":"none"}`), `hi is None` is an
in-tier `Compare [Is]` node, and the SOLE remaining `Unsupported` node per
function is the `Raise` guard — proof-side only, per the third row below.
Construct inventory, verified against the vendored bytes (the two functions
are construct-identical):

| Construct (exact counts per function) | Tier status |
|---|---|
| 4 params `(a, x, lo=0, hi=None)`, both defaults **Constant** (`0`, `None`) | ~~`args_unsupported: "defaults"`~~ → **F1 LANDED** (params carry `default` payloads; call arity window `nparams − ndefaults ≤ n ≤ nparams`) |
| `hi is None` → ~~envelope `Unsupported Compare:Is`~~ | **F2 LANDED** (`Is`/`IsNot` in tier iff one side of the link is the literal `None`) |
| `if lo < 0: raise ValueError('lo must be non-negative')` → `Unsupported Raise` (the `ValueError` call is inside it) | **NO tier growth** — statement is refused only if reached; theorems take `lo ≥ 0` (default `lo=0` satisfies it). rsa_inverse precedent. |
| docstring (`Expr` + `Constant:str`), `hi = len(a)` (`Call:len`), `while lo < hi` (`Compare:Lt`), `mid = (lo+hi)//2` (`BinOp:Add`, `BinOp:FloorDiv`), `a[mid] < x` (`Subscript`, `Compare:Lt`), `lo = mid+1` / `hi = mid` (`Assign`), `return lo` | all in-tier today |
| Full histogram per function: Assign 4 · BinOp:Add 2 · BinOp:FloorDiv 1 · Call:len 1 · Compare:Lt 3 · Constant:int 3 · Constant:str 1 · Expr 1 · If 3 · Name 17 · Return 1 · Subscript 1 · While 1 · Unsupported{Raise, Compare:Is} | — |

**Verdict: claim is 95% right, one loud caveat.** The construct list has a
*third* off-tier item — the `raise ValueError` guard — but it demands no tier
feature, only the `lo ≥ 0` hypothesis (automatic when using the defaults).
No other surprises: on this toolchain (Python **3.9.25**) there is **no
keyword-only `key` parameter** (added in 3.10 — vendoring from a newer
CPython would have brought keyword-only args into Band A) and **no slicing**
anywhere in either function.

### Band-A tier growth — LANDED 2026-07-30 (as-built record)

**F1 — literal parameter defaults** (shipped exactly as planned, with one
sharpening: "constant" tightened to *literal* — `ast.Constant` of
int/bool/str/None; a negative number `lo=-1` parses as
`UnaryOp(USub, Constant)` and is therefore non-literal, out of tier).
- Envelope schema: a param object MAY carry `"default": <const>` (existing
  const encoding), emitted only when present — verified: all 17 existing
  envelopes byte-identical on re-extraction; default-free params keep
  exactly the two historical keys.
- Extractor: literal defaults clear `args_unsupported`; ANY non-literal
  default (Name, negative number, call, `[]`) keeps
  `args_unsupported: "defaults"` with NO `default` keys — mixed
  literal/non-literal included. `*args`/kw-only/`**kwargs`/decorators
  unchanged (still refused).
- Lean: `Param.default : Option Const`; `callFunction` arity rule is the
  window `nparams − ndefaults ≤ nargs ≤ nparams` (`arityOk`, with
  `arityOk_full` embedding the old exact rule); `mkCallEnv` fills omitted
  trailing params (`defaultBindings`). Def-time-vs-call-time: CPython
  evaluates defaults once at `def` time; for literals, call-time filling is
  observationally identical (nothing to mutate/rebind) — the mutable-default
  footgun is unrepresentable by the literals-only rule. Arity violations →
  one canonical `TypeError` message (the harness compares exception class
  names, so CPython's per-case wording differences are immaterial).
- Surface: `py_check`/`py_prove` inherit the window through the interpreter;
  the VC bridges got general-arity forms (`PyTriple.callsTo_arityOk`,
  `…exists_callsTo_arityOk`, `…exists_callsTo_toVal_arityOk`,
  `…raises_arityOk` — every pre-existing bridge theorem keeps its exact
  statement as an exact-arity corollary) and `py_vcgen` applies the general
  forms, so `f(x) ==> v` with omitted optionals walks end-to-end
  (VCTests.lean `scale` smoke: arities 1 and 3, `#py_check` at 1/2/3).
- Differential rows: `Examples/python/opt_args/` — 38 CPython-vs-Lean calls
  across 8 functions (with/without optionals, too-few/too-many → TypeError,
  int/str/bool/None defaults) — all green.

**F2 — `is` / `is not` with a literal `None` side** (shipped as planned).
- Extractor: `Is`/`IsNot` survive per-link IFF one side of that comparison
  link is the literal `None` (either side); chained `x is None is None` is
  in-tier, `x is y is None` is not (first link). Everything else stays a
  whole-node `Unsupported "Compare:Is[Not]"` — identity on ints/strs is
  CPython-implementation-defined (small-int caching, interning).
- Lean: `x is None ⟺ x = Val.none` (`Val.isNone`); `is not` its negation;
  a hand-built AST comparing two non-`None` values is refused loudly.
  Chain/evaluation-order rules unchanged.
- Differential rows: in the same opt_args suite — `is None`/`is not None`
  over ints and `None` (flowing through defaults and intra-module calls,
  since the harness CLI passes ints only), both branches, `None is None`.

**Explicitly NOT needed for Band A**: Raise/Try, ValueError, keyword-only
args, slices, Attribute, any new builtin. Flagship theorem shape (spec
layer of DESIGN.md): for `a` a sorted int list,
`CallsTo m "bisect_left" #[.list a, .int x] (.int i)` with
`0 ≤ i ≤ a.size`, `∀ j < i, a[j] < x`, `∀ j ≥ i, x ≤ a[j]` — the two-arg
call exercises **both** defaults, and `lo = 0` discharges the guard.

**FLAGSHIP LANDED (2026-07-30)**: exactly that shape (surface form, `⇓`
and `==>`), proved by two independent cold prover agents and adapted into
`Examples/python/bench_bisect/{spec,proof}.lean` — plus strengthenings the
plan did not ask for: UNCONDITIONAL termination (any list, no sortedness)
and the deterministic `takeWhile`-length value forms. "Explicitly NOT
needed" held: the proofs use no Raise/Try/keyword/slice/Attribute/builtin
support. What the plan did NOT predict: both loop proofs had to leave the
`py_vcgen`/`py_loop` path because the body creates `mid` on its first
iteration (see "Cold-prover runs" below, framework fix F-2).

## Flagship plan: `heapq._siftdown`/`_siftup` and `statistics` medians

The two unproved flagships, and what each one actually needs (2026-07-31):

**heapq sift (rows 31–32, Band C)** — the real CPython runtime code (the C
accelerator does not replace the underscore helpers). Spec shape: the
returned/updated list is a permutation of the input that restores the heap
invariant on the affected range — an inductive argument over the
parent-chain walk, flagship-grade. Blockers: `Subscript-store`,
`BinOp:RShift` (cheap), and the hard one, **caller-visible mutation** —
value semantics cannot show the caller the in-place writes. This is the
designated driver for the reference-type/heap tier (the `~ref~` design
banked in the heap-tier notes): the benchmark's next tier investment should
be justified by this pair, not by more census rows.

**statistics medians (rows 29–30, Band C)** — `median_low`/`median_high`
are *one tier feature away*: `call:sorted`. Their empty-input
`raise StatisticsError` guard falls under the unreached-guard rule (theorems
take `data ≠ []`, same as bisect's `lo ≥ 0`), so no Try/Raise tier growth is
needed. Spec shape: order statistics — the result is an element of the data
with the ⌊(n−1)/2⌋ / ⌈(n−1)/2⌉ rank characterization (at least k elements
≤ it, at least n−k ≥ it) — stated over symbolic data, not just "index into
sorted()". `median` proper (row 28) stays a frontier marker: its
even-length branch is float division, honestly out of `Val` v0. `mean` via
exact `_sum` (census reference) is the long-game statistics target once
Fraction machinery is in reach.

## Cold-prover runs (2026-07-30)

Method: four INDEPENDENT fresh agents ("cold provers"), each given only a
target name and told to work from the repo's own docs (AGENTS.md,
`docs/**`, the example files) — no coaching, no tier edits allowed, all
scratch confined to `/tmp` (repo verified untouched afterwards). This is
the campaign's legibility measurement: can a stranger prove real targets
from the documentation alone? Every deliverable was re-verified at HEAD by
the landing pass: `lake env lean` exit 0; no `sorry`/`admit`/
`native_decide`; `#print axioms` = `[propext, Classical.choice,
Quot.sound]` on every audited theorem.

### Results

| Target | Outcome | Attempts (scratch artifacts) | Top stuck-point | Doc verdict |
|---|---|---|---|---|
| bench_bisect / `bisect_left` (Band A flagship) | **PROVED** — 4 theorems, incl. unconditional termination (no sortedness hypothesis at all) | 1 deliverable + 6 probe files | the loop body CREATES `mid` on iteration 1 (`Env.set` appends a slot), so the documented `py_vcgen`/`py_loop` recipe cannot align the loop state; fell back to hand-instantiating `execWhile_total_of_invariant` with an `Option Int` mid-slot and a hand-transcribed loop AST (`#guard`-checked against the loaded envelope) | docs sufficed end-to-end (`py_threshold`, `py_simp`, `execWhile_at_least`, threshold discipline all used as documented); the growing-env case was UNdocumented — goal-shape row added to AGENTS.md this pass |
| bench_bisect / `bisect_right` (Band A flagship) | **PROVED** — ∃-form total correctness (CPython's docstring contract); landed strengthened (see adaptation deltas) | 1 deliverable + ~40 probe/iteration artifacts | same growing-env wall, modeled as a `grown : Bool` flag; the costliest part was splicing the loop lemma back into `callFunction` (the `py_begin` entry lemma + `execWhile_at_least` + a hand-found fuel offset) | same verdict as prover 0; the loop-splice dance consumed most of the ~35 compile iterations — packaged-lemma/tactic candidate (fix F-3) |
| bench_iso7064_mod_11_10 (`checksum`/`calc_check_digit`/`validate`/`is_valid`) | **BLOCKED-CONFIRMED** (honest negative): proved the blockage itself as theorems — every call `.timeout ∨ .unsupported` for EVERY argument and fuel, hence no `==>` and no `==>!` — plus algorithm-level model correctness (roundtrip, uniqueness, substitution detection, transposition counterexample) validated against 120 CPython ground-truth rows | 1 deliverable + 6 probes | the tier gap exactly as the scoreboard said ({For, call:int} / {Try} / {call:str}); NEW finding: `calc_check_digit`'s `str(...)` makes v0 raise `NameError("str")` where CPython returns `'3'` — loud in outcome, wrong in KIND (fix F-1) | scoreboard rows 5–8 and surprise #2 ("check the interpreter, not the envelope") both confirmed EXACT; the tasking pointed at a nonexistent dir name (`bench_stdnum`) and the prover recovered from the scoreboard table alone |
| "luhn or Band B" (fallback taken: bench_calendar / `isleap` + `leapdays`) | **PROVED** — `isleap`, `leapdays` closed form, AND the per-year reference-count theorem (`leapCount`) | 2 attempts + 5 spike files | none on the final target (`py_prove`, one `Nat` induction, `omega`); the real work was verifying read-only that every Luhn-suite function is genuinely tier-blocked before invoking the offered fallback | benchmark.md's provable-now labels were accurate and actionable; the `#py_check`-first house rule was followed from AGENTS.md alone |

Score: **3 of 4 targets proved; the 4th target was tier-blocked by design
and the prover proved the blockage rather than faking progress** — the
"loudly, never wrongly" property held under adversarial-ish use.

### Adaptation deltas (cold deliverable → landed tree)

Statements were only ever STRENGTHENED, never weakened:

- `bisect_left`: landed verbatim. Cosmetics: support namespace
  `ColdBisect` → `BL`; `bisect_core` → `bisect_left_core`; one unused
  helper (`indexVal_toVal`) dropped.
- `bisect_right`: the cold ∃-form claim landed unchanged as
  `bisect_right_total`; landing added `bisect_right_terminates`
  (unconditional — required re-deriving the loop obligations under a
  bounds-only invariant), `bisect_right_sorted` (deterministic
  `takeWhile (· ≤ x)` value), `bisect_right_insertion_point` (`⇓`), and
  `bisect_right_partial` (`~~>`), for API symmetry with `bisect_left`.
  Two scratch `example` probes dropped; two `unusedSimpArgs` lints
  silenced by `set_option … in`.
- `bench_calendar`: landed verbatim (statements unchanged); `leapCount`
  moved into the proof namespace; 22 differential rows added to
  `harness/cases.json` (all green vs CPython 3.9.25).
- `bench_iso7064_mod_11_10`: the scratch file's tier theorems and model
  development were NOT landed (blocked target ⇒ checks-only census spec
  per the house layout); its interpreter-status rows landed in
  `spec.lean`, and its stuck-point analysis is quoted verbatim below.

### Stuck-point analysis, verbatim (the blocked target)

From the cold deliverable's header
(`/tmp/coldprover_iso7064_mod_11_10/iso7064_mod_11_10.lean`, the file's
own "honesty contract" — reproduced verbatim as the legibility record):

> 1. No positive `==>` theorem about these functions is provable through
>    the repo's definitional interpreter today — and this file PROVES
>    that, not just asserts it: `checksum_run`/`validate_run`/
>    `is_valid_run` show every call either times out or is refused loudly
>    (`Res.unsupported`, naming the out-of-tier statement), for EVERY
>    argument value and EVERY fuel. That is the framework's "loudly,
>    never wrongly" guarantee, instantiated as kernel-checked theorems.
>    Corollaries kill both arrows: no `==>`, no `==>!` (checksum/
>    validate/is_valid never return AND never raise).
>
> 2. `calc_check_digit_run` documents a FIDELITY ARTIFACT: its body's
>    `str(...)` call hits the v0 name-resolution rule (local env → module
>    functions → builtin `len` → NameError, docs/DESIGN.md "Name
>    resolution"), so the v0 semantics *raises* `NameError("str")` where
>    CPython returns `'3'`. The positive `==>!` theorem below is a true
>    statement about the v0 model and a FALSE statement about CPython —
>    stated only to pin the gap (cf. docs/benchmark.md "surprise #2":
>    check claims against the interpreter, not the envelope).
>
> 3. The functional correctness of the *algorithm the vendored code
>    implements* is proved against a Lean model transcribed line-by-line
>    from the vendored bytes (Python `%` = `Int.fmod`, `check or 10` =
>    truthiness fallback, fold init 5). The model is differentially
>    validated against CPython 3.9.25 running the actual vendored file on
>    40 inputs x 3 functions (120 `#guard` rows below, generated
>    2026-07-30, stdnum exception classes injected per the vendoring
>    rule). Proved: range (every checksum state is a digit 0..9);
>    `checksum_append_calc` (the roundtrip
>    `validate(number + calc_check_digit(number))` succeeds — for EVERY
>    `List Int`, no digit hypothesis needed); `calc_check_digit_unique`
>    (it is the UNIQUE such digit); `substitution_detected` (THE point of
>    ISO 7064 — every single-digit substitution error changes the
>    checksum, hence is caught); `isValid_iff`
>    (`is_valid n = true ↔ checksum n = 1`, incl. the empty-string
>    truthiness corner of `bool(validate(number))`);
>    `transposition_not_detected` (the adjacent-transposition guarantee
>    is REFUTED by witness — `checksum "56" = checksum "65"`, and both
>    "560" and "650" validate; CPython concurs on all four facts).
>
> 4. The INTENDED bridging spec — `iso7064.checksum(s) ==> checksumStr s`
>    — is not merely unproved: its negation is a theorem of the current
>    tier (`checksum_no_result`). It becomes provable exactly when
>    {For-over-str, call:int} land (docs/benchmark.md projection row).

### Framework fixes indicated (NOT implemented this pass — next wave)

- **F-1 (semantics, fidelity-in-kind)**: builtin names in call position
  (`str`, `int`, `bool`, …) fall through v0 name resolution to
  `NameError` — the model RAISES where CPython RETURNS. The refusal is
  loud but of the wrong kind (`.exn`, not `.unsupported`); it can make a
  `==>!` theorem that is false of CPython. Until call:str/int/bool land,
  unresolved names that are Python builtins should refuse
  `.unsupported`. Found by cold prover 2; pinned in-tree by the
  `calc_check_digit` row of `bench_iso7064_mod_11_10/spec.lean` (that
  row must flip, never be deleted). Differential-harness rule: any such
  change goes through `harness/cases.json` rows first.
- **F-2 (proof layer)**: loops whose body CREATES a variable on the
  first iteration (CPython's `mid = (lo+hi)//2` idiom) defeat
  `py_vcgen`/`py_loop` — both Band-A provers independently fell back to
  hand-instantiated `execWhile_total_of_invariant` with an
  `Option`/`Bool` env-shape flag. Teach the loop tactics an env-growth
  story (pre-roll the first iteration or normalize the env), or package
  the hand pattern. Interim: goal-shape row added to AGENTS.md
  (this pass), pointing at `Examples/python/bench_bisect/proof.lean`.
- **F-3 (proof layer, ergonomics)**: splicing a proven `execWhile` run
  back into `callFunction` (`py_begin`'s `hentry` + `execWhile_at_least`
  + hand-found fuel offsets like `fl + 26`) is where prover 1 burned
  most of its ~35 iterations. A packaged splice lemma/tactic that hides
  the offset arithmetic would cut flagship-class proof cost the most.
- **F-4 (harness)**: `leanmodels-run` parses CLI args as ints only, so
  the PROVED flagship has no `harness/cases.json` rows — the
  highest-value differential targets are exactly the list/str-taking
  ones. Extend `parseCli` with list/str literals.
- **F-5 (tier growth, already projected)**: {For-over-str, call:int,
  call:str, IfExp} → 9/33 proved-able; + {Try, Raise, call:bool} →
  13/33. Cold prover 2 re-confirmed these are the exact blockers on the
  iso7064 quartet (and would make its 120-row validated model the
  ready-made spec layer).
- **F-6 (library)**: all three proving agents re-derived the same
  marshalled-list indexing lemmas (`arr_getD`/`arrVal_getElem`/
  `getD_eq_getElem`, sorted-`Pairwise`-to-`getD` monotonicity,
  `takeWhile`-length characterizations). Promote them from
  `bench_bisect/proof.lean` into a shared list-spec lemma file.
- **F-7 (notebook tooling, found by this landing's CI run)**: the
  `%%lean` magic's `NotebookHeader` cache (`tools/lean_magic.py`,
  `_rebuild_header`) keys on the envelope set only — NOT on the
  `LeanModels` build — so any ABI change (F1's `Param.default` field)
  leaves a stale `notebooks/work/NotebookHeader.olean` and the notebooks
  CI step fails with kernel `Param.mk` arity mismatches until the
  gitignored cache is deleted by hand. Include the `LeanModels` olean
  fingerprint (or `lake` build stamp) in `_header_key`.

## Surprises found while vendoring (loud list)

1. **The bisect claim was missing the `raise` guard** (`if lo < 0: raise
   ValueError(...)`) — harmless (unreachable-branch argument) but it must be
   stated: the envelope contains an `Unsupported Raise` node and the theorem
   carries `lo ≥ 0`.
2. **`'%02d' % n` masquerades as in-tier** (row 15): `BinOp:Mod` is an
   allowed envelope node, so no syntax census flags it; only the interpreter
   knows (`.unsupported "'%' string formatting"`). Any future "provable-now"
   claim must be checked against the *interpreter*, not the envelope.
3. **easter's default is a `Name`, not a constant** — F1 (constant defaults)
   does not unlock it; module-constant defaults are a separate, harder
   feature (def-time evaluation / global folding).
4. **verhoeff/damm cannot be vendored runnable at all** in v0: their table
   constants live at module level and `callFunction` has no globals. A
   whole blocker class ("module-globals") that per-function syntax censuses
   do not surface.
5. The three iso7064 `validate` segments (and the three `is_valid`) are
   **byte-identical across modules** (equal segment sha256) — one proved
   spec shape will replay three times.
6. Vendoring from Python 3.9.25 (not 3.10+) is load-bearing for Band A:
   3.10's `bisect` adds keyword-only `key=None`, which would drag
   keyword-only args into the flagship's minimal feature set.

## Regeneration / verification

- Envelopes: `python3 extractors/python/extract.py Examples/python/bench_*/bench_*.py`
  (byte-stable; no `# lean[` blocks, so no companions are generated).
- Proofs: `lake build` from the repo root (the `Examples` glob picks up
  `bench_bisect/{spec,proof}.lean`, `bench_calendar/{spec,proof}.lean`,
  `bench_iso7064_mod_11_10/spec.lean`); axiom audit: `#print axioms` on
  each spec-side theorem must print exactly
  `[propext, Classical.choice, Quot.sound]`.
- Differential rows: `python3 harness/diff_test.py` (includes the
  bench_calendar isleap/leapdays rows; bisect/iso7064 rows are
  inexpressible — CLI is int-only, see fix F-4 — their concrete runs are
  `#py_check`/`#guard` lines in the spec files instead).
- Byte-verbatim audit: each vendored docstring lists original file sha256 +
  line ranges + per-segment sha256; slice those lines from the original and
  compare hashes.
- Originals: CPython files from this machine's `/usr/lib64/python3.9/`;
  PyPI sdists pinned by sha256 in each header (`pip download --no-deps`,
  2026-07-21): python_stdnum-2.2 `e95fcfa858a7…`, luhn-0.2.0
  `917174cecce8…`, python-dateutil-2.9.0.post0 `37dd54208da7…`.
- Authenticity: every vendored module was executed against its upstream
  (installed stdlib / unpacked sdist) on the sample inputs recorded in its
  docstring — all agree (2026-07-29, Python 3.9.25).
