# The C23 goal — the suite census, and what "conformance" is scored against

**Status: the endgame charter. Thomas ruled option (c)** of
`docs/c-tier-charter.md` §3 — the general C completeness ladder — and
attached a measurable definition: *"Is there a standard test suite for
C23? We should use that as the goal."*

**There is no official ISO conformance suite.** ISO publishes the
standard, not a test corpus; the suites that exist are compiler projects'
own testsuites and two commercial products. So the goal is restated in
the form the project can actually score:

> **The Lean semantics, RUN on suite programs, reproduces the suites'
> expected behavior** — scored MATCH / REFUSE / DIVERGE with the
> zero-DIVERGE invariant, exactly the Python census pattern.

`tools/ctwin/sunfish.c` stays **rung 0**, the driver fixture already
ingested (`docs/backlog.md` §L50). The twin-bridge theorem remains a
later option, not the goal.

This document is the CENSUS that has to come before pricing. Every number
below was measured by `harness/c_suite_census.py` on a pinned revision;
machine-readable rows in `docs/c23-suite-census.json`. Nothing is quoted
from memory.

---

## 1 The candidate corpora, measured

Pinned revisions and licenses in §2. `reachable` = the test parses under
the pinned profile, uses no construct outside rung 0's 45-kind vocabulary
**that the test actually wrote**, and needs no hosted libc header.

| corpus | tests | censused | parsed | in-vocab (written) | freestanding | **reachable** | oracle |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| **c-testsuite** | 220 | 220 | 219 | 201 | 157 | **147** | expected stdout |
| **gcc.c-torture/execute** | 1918 | 300 | 246 | 206 | 231 | **196** | exit status |
| **gcc c23-\* (dg-do run)** | 76 | 76 | 48 | 27 | 32 | **11** | exit status |
| **clang test/C/C23** | 37 | 37 | 12 | 3 | 11 | **3** | diagnostics, not behavior |
| **fujitsu/C** | 37191 | 300 | 300 | 283 | 0 | **0** | expected stdout |

Two of the five are sampled (`gcc.c-torture` and `fujitsu`, first 300 by
path); the rest are complete. The sampling is recorded in the JSON and
the Fujitsu sample is **not representative by construction** — it is the
first directory, which is math-heavy (§4.3).

### 1.1 The measurement that moved every number: written vs synthesized

The raw "outside the vocabulary" counts were dominated by attribute nodes
— `BuiltinAttr` 275, `NoThrowAttr` 267, `NoInlineAttr` 52 across the
corpora. **Those are not constructs any test wrote.** Measured:
`gcc.c-torture/execute/20000313-1.c` contains the text `void abort
(void);` and **zero** occurrences of `__attribute__` or `__builtin`, yet
its AST carries `BuiltinAttr` and `NoThrowAttr` — clang synthesizes them
on the declaration of a name it knows as a builtin.

Counting the compiler's own bookkeeping as the test's vocabulary inflates
every out-of-reach number. With synthesized attribute nodes set aside,
the torture suite goes from **7 in-vocab to 206** — a 29× correction, and
the difference between "this corpus is unreachable" and "this corpus is
the second-best rung-1 target we have." The instrument reports both and
the charter prices against the *written* number.

### 1.2 The two verdict styles — and one of them needs no output at all

The corpora do not share an oracle shape, and the split is load-bearing:

* **Expected-stdout** — c-testsuite (a `.expected` file beside each test)
  and Fujitsu (the tests print `OK`/`NG`). Scoring these requires
  modeling whatever produces the bytes.
* **Exit status** — GCC's torture and c23 run-tests. The idiom is
  `abort()` on failure, fall off `main` on success. Measured: torture's
  top calls are `abort` 162, `exit` 95, `__builtin_abort` 72 of 246
  parsed; c23-run's are `abort` 18, `exit` 17.

**The exit-status corpora are scoreable with ZERO output modeling**, and
the C tier already specifies exactly what they need: the architecture
memo §6 makes `abort` *"a distinguished TERMINAL outcome, not a
refusal."* So the largest reachable corpus is scoreable against machinery
the charter already committed to.

### 1.3 The libc surface is far smaller than "libc"

Measured distinct libc functions actually CALLED (not headers included):

| corpus | distinct calls | tests calling none | dominant |
| --- | ---: | ---: | --- |
| c-testsuite | 26 | **149** | `printf` (68) |
| gcc.c-torture/execute | 39 | 7 | `abort` (162), `exit` (95) |
| gcc c23-run | 23 | 19 | `abort` (18), `exit` (17) |
| clang C23 | 5 | 9 | `__builtin_*` only |
| fujitsu/C | 28 | 0 | `printf` (276), `puts` (24) |

**149 of c-testsuite's 220 tests call no libc function at all.** And
where libc is needed, the answer is not "model libc" — it is **model
`printf`**. That one function, plus `puts`, plus `abort`/`exit` already
specified, covers the overwhelming majority of all five corpora. The
format-string mini-language is its own small spec, which
`docs/c-extension-bridge-census.md` §5 already said in another context.

### 1.4 The preprocessor question, measured

The dispatch asked whether the suites assume a preprocessed translation
unit. **They do not** — they are raw `.c` files with directives, and they
lean on them: c-testsuite tags 96 of 220 `needs-cpp`, and Fujitsu's
sample is 283 of 300 by this census's own (narrower) measure of "uses a
directive beyond `#include`".

**This costs the tier nothing**, and that is a structural consequence of
a decision already taken: `docs/c-tier-architecture.md` §4 puts
translation phases 1-6 **outside Lean**, in clang. The preprocessor is
already not the Lean tier's problem, so `needs-cpp` tests arrive
pre-expanded and are scored on their expansion. The `c-0.1` envelope
already carries both spelling and expansion locations for exactly this
reason (`docs/c-envelope-schema.md` §2).

### 1.5 Why so many tests do not parse standalone

`parsed` is well below `tests` for the compiler-project corpora: 48 of 76
for gcc c23-run, 12 of 37 for clang C23, 246 of 300 for torture. These
are **not** broken tests — they are dg/lit tests that expect harness-supplied
options, and many are *designed* to be rejected. That is a category, not
a failure, and the instrument reports it as `parse-error` rather than
silently treating a partial AST as a small program.

It is also the reason **clang's C23 directory is bookkeeping, not a
behavior corpus**: 58 `-verify` and 17 `-fsyntax-only` RUN lines against
6 `-emit-llvm`. Its 37 tests map to 28 distinct WG14 N-papers by
filename (`n2322.c`, `n2350.c`, …), which is genuinely useful as a
**feature checklist** — a free per-paper index of what C23 added — and
almost useless as an execution corpus.

---

## 2 Licenses — and the recommendation is FETCH, DON'T VENDOR

| corpus | license | vendorable? |
| --- | --- | --- |
| c-testsuite *harness* | MIT | yes |
| c-testsuite *test cases* | **third-party**: 150 from `scc` (**ISC**), 69 from `tinycc` (**LGPL-2.1**) | **NO** — the tinycc-derived 69 |
| GCC testsuite (torture, c23-\*) | **GPL-3.0-or-later** | **NO** |
| clang `test/C` | Apache-2.0 WITH LLVM-exception | yes, with notice |
| Fujitsu compiler-test-suite | Apache-2.0 WITH LLVM-exception | yes, with notice |

**The c-testsuite license is a trap worth naming.** Its top-level
`LICENSE` is MIT and says, in its own first two lines, that it covers
*"all testing software, but not for individual test cases."*
`tests/LICENSE` then says the license of each case *"can be discovered by
a test case's `.otag` file."* Reading those 219 `.otags` is what produces
the split above: 150 cases originate in `scc` (ISC, permissive) and 69 in
`tinycc` (**LGPL-2.1**, copyleft). A lane that read only the top-level
MIT and vendored the directory would have redistributed LGPL code under
a wrong notice.

**GCC's testsuite carries no per-file license header** — measured: 0 of
the sampled torture files have one — so the files inherit the
repository's licensing, which is GPLv3+. Treat as GPL.

**Recommendation: fetch at test time, pin by revision, vendor nothing.**
It is the only policy that is uniformly correct across the five, it keeps
a 37k-file corpus out of the repository, and it costs nothing the project
does not already pay: the flagship corpus is *already* cross-repo
(`Examples/c/sunfish/` holds an envelope and no `.c`), and
`docs/c23-suite-census.json` already stores pinned revisions rather than
rows. The permissive two could be vendored; vendoring only those would
buy inconsistency.

**Commercial suites, recorded and NOT pursued.** Plum Hall's **CV-Suite**
and Solid Sands' **SuperTest** are the two industry C-conformance
products; SuperTest is the one most often paired with C23 claims. Both
are paid licenses with redistribution terms incompatible with an open
repository, so their tests could never be vendored and probably not even
committed as expected-output fixtures. What they would add over the free
corpora is *systematic* coverage — generated per-clause tests rather than
the regression-driven accretion GCC and clang testsuites are. **No
purchase is proposed and none was made; §5 lists it as Thomas's
decision.**

---

## 3 The verdict system

The Python lane's shape, adapted. The invariant is unchanged and is the
whole point: **DIVERGE must be zero, and REFUSE is never agreement.**

| verdict | meaning in C |
| --- | --- |
| **MATCH** | the model ran the program to completion and its observable equals the suite's expectation — the `.expected` bytes for a stdout corpus, or termination-without-`abort` for an exit-status corpus |
| **REFUSE** | the model declined, loudly and fuel-independently. Three disjoint causes, reported separately (§3.1) |
| **DIVERGE** | the model produced an observable and it DISAGREES with the suite. **The invariant violation. Zero, always** |
| **TIMEOUT** | fuel exhausted. The only exhaustion outcome; never conflated with REFUSE |

### 3.1 REFUSE has three causes and they must not be pooled

They retire on completely different schedules, so pooling them would make
the scoreboard unreadable:

1. **Out-of-tier construct** — the program uses something the vocabulary
   does not cover (`switch` today). Retires by climbing a rung. This is
   the Python lane's `.unsupported` exactly.
2. **UB, refused loudly** — the program's behavior is undefined and the
   model declines to invent one (`docs/c-tier-charter.md` §2.2(c);
   eleven classes armed). **Never retires** — it is the product. A suite
   test that is UB is a test the model is *right* to refuse, and some
   corpora contain them deliberately.
3. **Unmodeled libc** — the program calls a function outside the modeled
   slice. Retires by widening the slice, and §1.3 says the slice is
   small.

A fourth non-verdict, borrowed from the Python lane and equally
load-bearing: a run that executed **nothing** must never score as
agreement. The Python harness carries `"live"`; the C scoreboard carries
the statement count.

### 3.2 What MATCH means against an expected-stdout oracle

The suite's `.expected` file is a byte string, so MATCH is byte equality
against the model's `World.stdout` — the same "stdout is world data"
treatment the Python tier uses, which the architecture memo §6 already
specified for C. Two honest wrinkles, both to be settled when the
scoreboard is built:

* **Trailing newline and buffering.** The model appends chunks in
  emission order and never flushes; a real program's `stdout` buffering
  is not observable in the final bytes, so this should be exact. It is an
  assertion until the first row runs.
* **`printf` is a spec, not a call.** Matching bytes means implementing
  the conversion directives the corpora use — not all of them. That set
  is measurable before it is built, and measuring it is rung 2's census.

---

## 4 The rung ladder — measured, not proposed

`harness/c_suite_census.py` computes the greedy ladder over the **431
freestanding parsed tests** across all five corpora: at each step, add
the single construct that unblocks the most still-blocked tests.

| step | construct added | cumulative clear (of 431) |
| ---: | --- | ---: |
| — | *nothing* — the 45 kinds `sunfish.c` uses | **357** |
| 1 | `SwitchStmt` | 357 |
| 2 | `CaseStmt` | 361 |
| 3 | `ImplicitValueInitExpr` | 366 |
| 4 | `NullStmt` | 374 |
| 5 | `DefaultStmt` | 383 |
| 6 | `VAArgExpr` | 393 |
| 7 | `StaticAssertDecl` | 398 |
| 8 | `DesignatedInitUpdateExpr` | 403 |
| 9 | `VectorType` | 408 |
| 10 | `GenericSelectionExpr` | 411 |

`SwitchStmt` alone clears nothing — no test uses `switch` without also
using `case`, so the two are one step in practice and the greedy walk
just spends them in sequence. Steps 1-5 are the `switch` family plus two
one-liners (`;` as a statement, and the zero-initializer clang
materializes), and they are worth **26 tests** between them.

**Rung 0 already clears 357 of 431 — 83% — before anything is added.**
That is the census's most decision-relevant number and it was not
predictable: it says the flagship corpus's accidental vocabulary is a
good approximation of what real C test programs use, and that the ladder
above it is *short*. Eight constructs take it to 403.

The exact greedy order is in `docs/c23-suite-census.json`
(`reach_ladder`), regenerated by the instrument rather than transcribed.

**What the ladder does NOT include, and must not be read as including:**
this is reach of the *vocabulary*, i.e. what the ingester accepts. It is
not a claim that the semantics would run any of these tests — **there is
no semantics yet.** M2 builds it. The ladder prices which constructs to
build first; it does not price building them.

### 4.1 The rungs in scoring terms

* **Rung 0 (now)** — `sunfish.c` ingested. No scoreboard: nothing runs.
* **Rung 1** — the exit-status corpora at rung-0 vocabulary: **196
  reachable** in the torture sample, needing only `abort`/`exit`, which
  the charter already models. This is the cheapest first scoreboard in
  the whole program and it needs no output modeling.
* **Rung 2** — `printf`, which unlocks c-testsuite's stdout half (68
  tests) and most of Fujitsu.
* **Rung 3+** — the construct ladder above, each rung a census of what it
  unblocks before it is built.

### 4.2 The scoreboard instrument — specced, not built

`harness/c_refusal_census.py`, the sibling of the Python lane's
`harness/refusal_census.py`. **It is not built here**, because it has
nothing to run until M2's interpreter skeleton exists, and an instrument
with no subject is a stub. The spec:

* input: a corpus directory plus its oracle convention
  (`expected-stdout` | `exit-status`), and a pinned revision;
* per test: extract (`extractors/c/extract.py`), ingest, run under fuel,
  compare to the expectation, emit **one row per test in test order**;
* one runner process for the whole batch — the lesson recorded three
  times in `docs/backlog.md` (615 rows went from hours to ~11 s);
* verdicts of §3, with REFUSE broken out by its three causes;
* exit non-zero on any DIVERGE, and never on a REFUSE;
* an unexecutable test emits a `runner-error` row rather than no row, so
  the count stays honest;
* **no whitelist for silencing a mismatch** — the standing prohibition.

### 4.3 The honest scale statement

* **Language versus library.** C23 is a language *and* a library clause,
  and this goal is scoped to the LANGUAGE. The library appears only as
  the slice the corpora call (§1.3). A "C23 conformance" claim covering
  clause 7 is not what this ladder builds and should never be worded as
  if it were.
* **The corpora are not a specification.** They are three compiler
  projects' regression histories plus one vendor's suite. High scores
  mean "agrees with what these projects test", not "conforms to ISO
  9899:2024". The commercial suites are the ones that claim clause
  coverage, which is precisely what they sell.
* **Floats recur, and stay a named Thomas-decision.** The Fujitsu sample
  is math-heavy (`fabsf` 13, `fabs` 8, `copysign`, `cos`, `fmod`, and
  `complex.h` in 7 of 300), and `docs/c-profile.md` already records that
  **neither development host defines `__STDC_IEC_60559_BFP__`** — neither
  claims Annex F. So a float rung would be differential-testing against a
  contract neither side signed. The charter's R4 gate stands unchanged
  and this census only sharpens why. Same shape as the Python side's
  float decision.
* **Sampling.** Two corpora are sampled at 300. The Fujitsu sample is the
  first directory by path and is math-heavy; a stratified sample is owed
  before any Fujitsu number is used for pricing.

---

## 5 Decision points — Thomas's, listed explicitly

1. **Commercial suite purchase — yes/no.** Plum Hall CV-Suite and Solid
   Sands SuperTest. What they add: systematic per-clause coverage instead
   of regression accretion. What they cost beyond money: their tests
   cannot be vendored or, most likely, quoted in the repository, so they
   would be a private scoreboard beside the public one. **Nothing was
   purchased and nothing is proposed.**
2. **Vendored versus fetched corpora.** The recommendation is
   **fetch-don't-vendor with pinned revisions**, uniformly (§2). The
   alternative worth considering is vendoring only the two
   Apache-2.0 corpora; it is legal and it buys reproducibility at the
   cost of an inconsistent policy and a large repository.
3. **The float modeling approach, when its rung arrives.** Options, in
   the charter's terms: (i) exact-only, admitting values, assignment and
   comparison and refusing every rounding operation — what
   `docs/c-tier-charter.md` already specifies for v0; (ii) a full IEC
   60559 tier, gated on a toolchain that *declares* Annex F, which
   neither current host does; (iii) an explicitly scoped non-Annex-F
   claim. This blocks the Fujitsu math corpus and nothing before it.

Still open from earlier and unchanged: **sunfish PR #256** (`SF_PYREF`),
awaiting review.
