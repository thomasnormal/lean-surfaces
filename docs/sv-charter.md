# The SystemVerilog tier: FOUNDING CHARTER

**Status: the workstream's founding document.** The owner chartered the
language-family programme with *"System Verilog also has a spec, that we
can similarly follow"* — versioned surfaces, spec-mirror as the general
behaviour — and this charter founds the SV lane on the C tier's proven
template (`docs/c-tier-charter.md`, §L35): census first, corpus and
licence surveyed per-file, taxonomy mapped, first milestone planned.
**No Lean semantics in this pass. No existing file changed.**

**It recommends no endgame.** §6 presents them; §8 lists what the owner still has to
answer.

---

## 0 THE CORRECTION THIS CHARTER OPENS WITH

The C tier was chartered onto a blank page: `LeanModels/C/` did not
exist, and the charter's job was to decide whether it should. **The SV
lane is not that, and a charter that pretended otherwise would be
wrong on line one.**

Measured today, on this clone, at `426fdb7`:

| | files | lines |
| --- | ---: | ---: |
| `LeanModels/Sv/` | 14 | **8 166** |
| `extractors/sv/` | 3 | **3 583** |
| `Examples/system-verilog/` | 18 designs + envelopes | — |
| `harness/sv/` | 8 | — |

`find LeanModels/<tier> -name '*.lean'`, summed. That makes SV the
**third-largest tier in the repository**, behind Python (32 331) and
Spice (23 366) and ahead of Circuit (4 309), Rv (2 041), C (934) and
VerilogA (606). It carries **86 `theorem`/`lemma`/`example`
declarations, zero `sorry`, zero `native_decide`** (`grep -rc` over
`LeanModels/Sv/*.lean`).

So this is not a founding in the sense of *starting*. It is a founding
in the sense the C charter meant when it found M0 already done and the
record not knowing: **the SV tier was built to a real milestone, then
went dormant, and the charter's first duty is to re-measure it and
correct the record.**

**The dormancy, dated.** The last commit touching `LeanModels/Sv`,
`extractors/sv` or `Examples/system-verilog` is `db9bb3e` *"CV32E40P
phase 2: symbolic sv-0.2 ingestion + semantic tier, dual-sim
validated"*, **2026-07-31**. `git rev-list --count db9bb3e..HEAD` =
**318**. The lane has been untouched for three weeks and 318 commits of
sibling traffic.

**What that dormancy did NOT break — every claim below is a run made
today, not a citation.**

1. **The differential harness is GREEN.** `python3 harness/sv/diff_test.py --sim iverilog`
   → **10 cases, 10 PASS, `overall: PASS`** against Icarus Verilog
   12.0. Nine matched `sigma_src`; `race_blk_one_edge` matched
   `sigma_rev` — i.e. the schedule oracle is not decoration, the racy
   example really does need the other schedule and the harness really
   does try it.

2. **The extractor still round-trips BYTE-IDENTICALLY.** Re-running
   `extractors/sv/extract.py` over every pinned source in
   `Examples/system-verilog/` and diffing against the committed
   envelopes: **17 of 18 identical, 0 differing, 1 error.** Six are
   schema `sv-0.1` (single-file mode), eleven are `sv-0.2` (symbolic
   `--top` mode). The one error is
   `cv32e40p_register_file_ff`, which needs `cv32e40p_pkg.sv` from the
   external OpenHW checkout that is deliberately **not vendored** — an
   absent input, not a defect.

3. **The tier still builds.** `lake build` reached **3 690 of 3 693
   jobs with ZERO compilation errors**, and **all 14 `LeanModels.Sv.*`
   modules built**. Stated exactly, because the run did not exit 0: two
   targets — `Examples.python.sunfish.bound_depth` and
   `…pins_clock`, both in the *Python* tier — died with `Lean exited
   with code 143`. **143 = 128 + 15 = SIGTERM: they were KILLED, not
   failed**, under the machine contention that prompted the
   repository-wide build lock the same afternoon. No SV target failed
   and no diagnostic was emitted by any target. The honest claim is
   therefore *"the SV tier builds clean; the run was interrupted
   elsewhere"* — not *"the build is green."*

**A methodological note that belongs in the charter because it nearly
became a false finding.** The first round-trip run reported *12
differing*. That was the instrument, not the tree: the `sem2` envelopes
are `sv-0.2`, which requires `--top <module>`, and the loop had invoked
single-file mode. Re-run with the mode each envelope declares in its own
`schema` field, the differences vanished entirely. **An envelope
compared against the wrong extraction mode is a silent wrong answer of
exactly the C charter's kind**, and the rule it yields is now written
down: *read the mode out of the artefact, never assume it.*

---

## 1 THE CENSUS — and the four defects it found

### 1.1 The frontend is `pyslang`, and it is NOT installed

`extractors/sv/extract.py` requires **python3.12 + pyslang 11.x** — the
Python bindings to **slang**, an MIT-licensed SystemVerilog frontend.
This settles the "which frontend can emit a usable AST" question the
charter was asked to census: **the lane chose one three weeks ago,
wrote 2 495 lines against it, and validated the result on two
simulators.** Verilator was not the answer and re-litigating it would
be re-work.

But measured today:

```
$ python3.12 -c "import pyslang"
ModuleNotFoundError: No module named 'pyslang'
```

**The lane's frontend is absent from this host.** Priced: a clean
`python3.12 -m venv` + `pip install pyslang` yields **pyslang 11.0.0**
— inside the extractor's declared 11.x range — in well under a minute,
no build, no system dependency. Every extractor claim in §0 was made
through that venv. So the gap is *unpinned*, not *unavailable*, and the
fix is a recorded dependency rather than an engineering effort.

**Why slang and not Verilator, recorded so it is not re-asked.** The
envelope needs a *source-level* AST with elaborated widths. Verilator's
`--json-only` emits its own post-elaboration IR after aggressive
inlining and generate-unrolling; slang's compilation exposes the
elaborated symbol table *beside* the syntax tree, which is what lets
the envelope carry `sv-0.1`'s resolved widths **and** `sv-0.2`'s
symbolic parameter binders. Verilator is also not plain-permissive
(LGPL-3/Artistic dual), where slang is MIT.

### 1.2 The corpus census cites an artefact that is NOT in the tree

`docs/sv-corpus-coverage.md` states its machine-readable results live
at `harness/sv/conformance/census.json`. Measured:

```
$ git ls-files harness/sv/conformance/
harness/sv/conformance/runner.lean
harness/sv/conformance/unlockable.txt
```

**`census.json` is not tracked and not present.** The document's
headline numbers — 21 336 files walked, the construct-frequency table
that it calls *"THE IMPLEMENTATION PRIORITY QUEUE"*, the per-chapter
coverage — are therefore **unreproducible from this repository**: the
aggregates survive only as prose in the memo that cites the missing
file. The sibling `unlockable.txt` (11 lines) did land, which is how
§1.4 below could be measured at all.

### 1.3 The census instrument points at a path that does not exist

`extractors/sv/census.py:58`:

```
DEFAULT_CORPUS = "/home/thomas-ahle/mox/sv-conformance/sv-tests-2/tests"
```

An absolute path on a Linux host. `ls /home/thomas-ahle` → *No such
file or directory*. The reproduce-block in
`docs/sv-corpus-coverage.md` invokes `census.py` with **no `--corpus`
flag**, so the documented command cannot work on this machine.

The instrument itself is *fine* — pointed at a corpus with `--corpus`
it runs, and a 40-file smoke completed in **2.0 s**. The defect is
purely the hard-coded default, and it is the SV analogue of exactly
what `--compare` was invented for in the C tier: **a corpus that lives
outside the repository, with no mechanical staleness check.**

### 1.4 THE HEADLINE: the censused corpus is NOT the public one

This is the finding that most changes what the owner is deciding.

`docs/sv-corpus-coverage.md` censuses a corpus it calls **sv-tests-2**.
There is also `/Users/ahle/repos/sv-tests`, a clean checkout of the
public **chipsalliance/sv-tests**. The charter assumed, as any reader
would, that one was a checkout of the other. **They are disjoint.**

The decisive test — the 11 filenames `unlockable.txt` names, looked up
in the public suite:

```
present=0  missing=11
```

**Not one of them exists upstream.** They are not renamed; the public
suite has no `11.4.4--unsigned-comparison.sv`, no
`6.9.1--vector-unsigned-wrap-modulo-v3.sv`. The corpora are different
bodies of work.

Located and censused, read-only:

| | public `sv-tests` | `sv-tests-2` |
| --- | --- | --- |
| location | `~/repos/sv-tests` | `~/repos/mox/sv-conformance/sv-tests-2` |
| origin | `chipsalliance/sv-tests` | **inside `normal-computing/mox`** |
| `.sv` files | **1 028** tracked | **21 631** (21 186 under `chapter-*`) |
| chapter dirs | 20, clauses 5–26 | **38, clauses 3–40** |
| licence | **ISC, uniform, per-file SPDX** | **none — no LICENSE file** |
| redistributable | yes, with attribution | **no** |

`sv-tests-2`'s own README describes it as an *"IEEE 1800-2023
SystemVerilog conformance corpus, chapter-by-chapter … Owner:
fleet-wide"*, covering the full SV surface plus the VPI clauses.

**Three consequences, and the third is a hard blocker.**

1. **It is 21× the size and spans nearly twice the clause range.** It
   reaches clauses 27–40 — generate constructs, gate-level modelling,
   UDPs, specify blocks, timing checks, SDF, configurations, protected
   envelopes, DPI, and the whole VPI/assertion/coverage API surface —
   that the public suite does not test at all. As a *measuring
   instrument* it is far and away the better one.

2. **It is employer-internal.** It lives inside a
   `normal-computing/mox` clone. `lean-surfaces` publishes to
   `thomasnormal/lean-surfaces`. Anchoring a public repository's
   conformance claims to a private corpus means **no reader outside can
   reproduce a single coverage number** — and the coverage memo already
   depends on it.

3. **It embeds the IEEE standard itself.**
   `tests/chapter-36/ieee-1800-2023.pdf`, 9 448 927 bytes. That is
   copyrighted IEEE text. The family law is *no ISO/IEEE text
   vendored, cite-and-paraphrase only*; this charter reports the file's
   existence and size and **has not opened it**. Any future rule that
   vendors or mirrors `sv-tests-2` wholesale would drag that PDF along,
   and must not.

Per-file licensing inside `sv-tests-2` is the **c-testsuite trap in its
purest form** — not a *conflicting* licence, but *no licence at all*:
in `tests/chapter-11`, **3 of 1 005 files carry an SPDX tag.**

### 1.5 The public suite, censused per-file — and its own trap

Because §1.4 makes the public suite the *vendorable* candidate, it was
censused to the standard the family law demands.

**Provenance.** `chipsalliance/sv-tests` at
`4f24807559e90dd26cb887517e2fedae160f672f`, 2026-01-15, exactly at
`origin/master`. `tests/` is unmodified; the working tree is dirty only
in `tools/runners/Verilator.py` and untracked build outputs. 33
submodules declared, **32 uninitialised**.

**Structure — and it is already clause-mirrored.** 1 028 `.sv` tests
organised *by IEEE 1800 chapter*: `chapter-18` 134, `chapter-7` 103,
`chapter-11` 88, `chapter-6` 84, `chapter-22` 75, `chapter-8` 53,
`chapter-16` 53, `chapter-5` 50, and a 185-file `generic/` bucket.
Metadata is a `:key: value` header block; **all 1 028 carry `:name:`,
`:description:` and `:tags:`.**

**1 381 tag occurrences over 326 distinct tags** — and the tags *are
clause numbers* (`5.6.4`, `8.3`, `11.5.1`, `22.5.1`). `conf/lrm.conf`
is a **482-entry clause dictionary** (457 numeric LRM clauses + 25
suite tags), of which **324 are exercised and 158 have zero coverage**.

**This is the charter's happiest finding: the organising principle the
SV tier needs is already agreed by the corpus.** The C tier had to
*invent* a mapping from its census to the standard's structure. Here
the corpus is indexed by clause number natively, `lrm.conf` is a
ready-made clause dictionary, and a coverage claim can be stated
per-clause without building any of that scaffolding. The densest holes
are named: **clause 6 (48/92 covered), clause 11 (25/54)**, clause 18
(39/55), clause 9 (23/33) — and clauses 6 and 11 are precisely the
two the M0 tier is closest to owning.

**Negative tests — a refusal corpus, pre-labelled.** **80 of 1 028
(7.8%)** carry `:should_fail_because:` with free-text LRM prose
("switch variable not declared"; "it is illegal to do bit select on
real data type"). The runner defaults `should_fail` to true exactly
when that reason is non-empty, so **every negative test carries a
human-readable rationale**. That is the raw material for a refusal
taxonomy, with the honest caveat that the strings are **not a
controlled vocabulary** and would need clustering.

**LICENCE — the verdict, per-file.** Top-level is **ISC** (SymbiFlow
Authors). Across `tests/`: **1 029 SPDX occurrences, every one `ISC`,
zero other licences**; 1 028 of 1 030 files tagged; the two untagged
are `tests/README.md` and a two-line `.svh` include. A contamination
scan for *"all rights reserved" / Accellera / proprietary /
non-commercial / GPL / Apache / BSD / Solderpad / confidential* across
`tests/` returns **0 hits**. Single copyright holder, single licence,
no exceptions.

**But the trap is real, and it is one directory away.** The suite the
project's dashboard actually reports on is *generated*:
`make generate-tests` synthesises `tests/generated/` (gitignored) whose
`:files:` keys point straight into `third_party/`. Licences reachable
that way include **GPL-2.0** (`ivtest`, from Icarus — verified against
`~/repos/iverilog/ivtest/COPYING`), Solderpad 0.51, BSD-3, MIT.
`third_party/cores/black-parrot` is 2 504 files with **zero** SPDX
tags.

> **Vendoring rule, stated for the family: `tests/**` only, never
> `third_party/**`, never `tests/generated/**`.** Under that rule the
> public suite is ISC-clean and attributable. Outside it, the tree
> reaches GPL-2.0 in one hop.

### 1.6 The re-census: the M0 extractor against the PUBLIC suite

Because §1.4 makes the public suite the only vendorable anchor, the
committed instrument was pointed at it — the first time the SV
extractor has been measured on the corpus it might have to live on.

`python extractors/sv/census.py --corpus ~/repos/sv-tests/tests --jobs 8`

The instrument walks `tests/chapter-*` only, so it sees **717** of the
1 028 tests (the 185-file `generic/` bucket, `testbenches/` and
`uvm/` sit outside any chapter and are out of its scope by
construction).

**The run does not complete — and finding out why is the most
actionable result in this charter.**

Bisected on `--limit` (each run `nice -n 19`, 4 jobs):

| limit | result |
| ---: | --- |
| 100 | completes, **1.6 s** |
| 200 | completes, **1.5 s** |
| 400 | completes, **1.5 s** |
| **500** | **never completes** (killed at 120 s) |
| 600, 717 | never completes (killed at 120 s, and at 600 s) |

At `--jobs 1` it also never completes, and the process sits at **0.0%
CPU in state `S`** — it is not working slowly, it is *stopped*.

**The cause, isolated to one file.** Reproducing the instrument's own
walk order (`sorted(os.listdir)` over `chapter-*`, one level deep,
717 files) and running the extractor on each of files 400-510
individually, exactly one is fatal:

```
rc=133   chapter-22/22.9--unconnected_drive-invalid-2.sv
```

**133 = 128 + 5 = SIGTRAP.** Re-run alone, redirected: `TRUE_RC=133`
and **zero bytes of output**. The whole file is two directives:

```
`unconnected_drive pull2
`nounconnected_drive
```

— a *negative* conformance test (`:should_fail_because: The directive
`unconnected_drive takes one of two arguments - pull1 or pull0`).
**pyslang 11.0.0 hard-crashes the interpreter on it, with no
diagnostic**, and `census.py`'s `multiprocessing.Pool` then waits
forever for a result from a worker that no longer exists.

**Two defects, and both are "never hide errors" violations.**

1. **The frontend dies on valid input to the tool** — a two-line source
   file that a conformance suite is *supposed* to reject gracefully.
   Upstream-reportable; the lane cannot fix it, only contain it.
2. **The instrument turns that crash into a HANG**, which is strictly
   worse than a crash: a hang has no exit code, no message, and no
   failing file name. A worker death must be reported as a per-file
   `error`, never absorbed. The existing 90-second per-file
   `signal.alarm` cannot help, because the process carrying the alarm
   is the one that dies.

**This CORRECTS what this charter would otherwise have concluded.**
The draft of this section read *"the extractor runs on the public suite
unmodified, so switching the anchor corpus is a licensing decision, not
an engineering one."* **That is false, and only running it showed so.**
Switching corpora costs at least: a crash-containment layer in the
census (per-file subprocess isolation, so a SIGTRAP becomes a recorded
`error` row), and an upstream bug report. It is a small cost — but it
is not zero, and the owner should price decision §8.1 knowing it.

**What the partial run does establish**, on the first 400 files
(chapters 10-21, complete): **294 partial, 13 clean, 33
`skip_include`** at limit 400. The tier's M0 vocabulary covers a small
minority of the public suite cleanly, which is expected and consistent
with the `sv-tests-2` census's shape — the top blockers on the smoke
sample are `AssignmentExpression:target`, `VariableSymbol:signed`,
`NamedValueExpression:signed` and `VariableSymbol:range`, i.e.
**signedness and range metadata, not exotic constructs.**

**What the re-census cannot settle** is comparability: the two corpora
share no files, so public-suite numbers are a *new baseline*, not a
delta against `docs/sv-corpus-coverage.md`. Any claim that the tier's
coverage "changed" by switching corpora would be meaningless.

### 1.7 The family registry row — corroborated twice, and CORRECTED once

`docs/family-architecture.md` landed while this charter was being
written, and it carries a PROPOSED registry row for this lane:

| language | `<Lang>` | authority | edition tokens | oracle | corpus |
| --- | --- | --- | --- | --- | --- |
| SystemVerilog | `Sv` | spec-mirror — IEEE 1800 | `SV2017`, `SV2023` — **PROPOSED** | pyslang frontend; a simulator | sv-tests-2 |

The two lanes worked independently and agree on three things, which is
worth more than either saying it alone.

* **The edition split.** The family doc records SV as *"one lane, two
  editions"* — citing -2017 for operator semantics while censusing a
  -2023 corpus. This charter found the same inconsistency from the
  other end (§2.1). **Independently corroborated; §8.5 is the
  decision.**
* **`Circuit/` is not the divider's foothold.** The family doc warns
  that *"a founding lane that goes looking in `Circuit/` will find
  calculus"* and concludes the divider's circuit side is the SV tier.
  §6.1 reached that by censusing the 25 files. **Corroborated
  empirically.**
* **An instrument in the wrong tree.** The family doc names
  `extractors/sv/census.py` as the one violation of *"instruments live
  in `harness/`"*, to fix *"when the SV lane is next open."* **The lane
  is now open**, so SV-M1 adopts it (§7 inch 7).

**And one CORRECTION this charter owes the family doc.** The registry
row's corpus field reads **`sv-tests-2`** — which §1.4 measures as
employer-internal, carrying **no licence**, and embedding the IEEE PDF.
**A public repository's registry should not name a corpus its readers
cannot obtain.** The row cannot be ratified as written; §8.1 is the
decision that settles it, and until then the corpus field should be
read as PROPOSED in the strong sense — *unresolved*, not merely
provisional.

---

## 2 THE SPEC MAP — IEEE 1800

### 2.1 The versioned pair

The family directive is *versioned surfaces*. For SV the version
siblings are:

* **IEEE 1800-2023** — current. What `sv-tests-2` targets and what the
  charter treats as the reference edition.
* **IEEE 1800-2017** — the prior revision, and the edition
  `docs/sv-design-m0.md` actually cites for its 4-state operator
  semantics (§11.4.3 whole-vector collapse, §11.4.11 ternary merge).

**They are not far apart, and that is the point.** 1800-2023 is a
maintenance revision: clause numbering is stable across the core
simulation clauses, so a `-2017` citation and a `-2023` citation
usually name the same rule. The C tier's versioning problem (C99 vs
C11 vs C23 genuinely move semantics) is *milder* here — but the lane
already has a live inconsistency, citing -2017 in the design memo while
the corpus is -2023, and the charter's rule is: **cite the edition you
measured against, per claim, and never silently mix.**

No IEEE text is reproduced anywhere in this repository. Clause numbers
and paraphrases only.

### 2.2 The clause structure, classified

IEEE 1800-2023's ~40 normative clauses do **not** form one semantic
surface. Classified for the tier — this is what tells the owner which
clauses are *semantics* and which are *features*:

| class | clauses | what it means for the tier |
| --- | --- | --- |
| **Simulation semantics — THE HEART** | **4** (scheduling), 9 (processes), 10 (assignments), 11 (operators), 12 (procedural statements), 6–7 (data types/values) | must be modelled; every theorem depends on them |
| **Elaboration / static structure** | 3, 23 (modules), 25 (interfaces), 26 (packages), **27 (generate)**, 33 (configurations) | resolved *before* time starts; the `sv-0.2` symbolic mode is exactly this layer |
| **Lexical / preprocessing** | 5, 22 | frontend's job; slang already owns it |
| **Verification features** | 8 (classes), 13, 14 (clocking), 15 (IPC), 18 (constrained random), 19 (coverage), 24 (programs) | a *separate tier* — see §2.5 |
| **Assertions** | 16, 17 (checkers), Annex F | a temporal logic over the trace; its own semantic layer |
| **Structural / timing modelling** | 28 (gate-level), 29 (UDP), 30 (specify), 31 (timing checks), 32 (SDF) | legacy Verilog surface; low value, cleanly separable |
| **Foreign / API surfaces** | 34 (protected envelopes), 35 (DPI), 36–38 (VPI), 39 (assertion API), 40 (coverage API) | axiomatic boundaries, not semantics |
| **Annexes** | A (formal BNF), B (keywords), F (assertion semantics) | A and F are *gifts* — see below |

**Two annexes deserve naming.** **Annex A** is a complete formal
grammar — the SV analogue of nothing the C tier had, and a natural
completeness yardstick (*"which productions does the tier accept?"*,
exactly the shape of the Python lane's 86-production census). **Annex
F** gives concurrent assertions a formal semantics *in the standard
itself*, so clause-16 work has a normative target rather than an
interpretation.

### 2.3 THE SEMANTIC HEART: clause 4, priced

**Clause 4 (scheduling semantics) is the SV tier's centre of gravity,
and nothing else comes close.** C's semantic heart was a memory model
that had to be *invented* from prose scattered across §6.5 and Annex
J. SV's is one clause, and it is written as an operational algorithm.

The stratified event regions, per simulation time slot, in order:
**Preponed → Active → Inactive → NBA → Observed → Reactive →
Re-Inactive → Re-NBA → Postponed**, with iteration back to Active
until the time slot's events are exhausted. The PLI regions interleave.
This is what makes:

* nonblocking assignment (`<=`) mean *sample now, commit in NBA*;
* `always_comb` settle to a fixpoint within Active;
* clocking blocks and program blocks sample in Preponed and drive in
  Reactive — the whole point of clause 14 and 24;
* `$strobe`/`$monitor` see Postponed values.

**The pricing, and it is the charter's central architectural claim.**
The standard specifies the *regions* and their order, but **within the
Active region it explicitly permits the scheduler to pick any ready
process in any order.** That residual freedom is not an edge case; it
is where every race in every real design lives.

**What the tier already has, and what it does not.**
`docs/sv-design-m0.md` implements a **cycle-level** collapse of clause
4: comb-settle to fixpoint (σ-ordered) → edge phase (σ-ordered,
blocking assigns immediate) → NBA commit → comb-settle again. That is a
faithful projection of the Active/NBA split *at cycle granularity*, and
it is enough for the six M0 designs and the CV32E40P modules. It does
**not** model: `initial`, `#` delays, the Inactive region, Observed /
Reactive (so no clocking blocks, no program blocks), or Postponed.
`initial` and `#` are explicitly `Unsupported` today.

**Price to go from the cycle collapse to the full region ladder: this
is the largest single item in the lane's future**, and it is the one
that re-opens every existing theorem, because the trace type changes
from *one snapshot per cycle* to *one per time slot with region
structure*. The charter's recommendation is to price it as its own
milestone and not to smuggle it into a feature milestone.

### 2.4 The refusal taxonomy, and how ∀-resolution generalises

The C tier fixed three causes that never pool
(`docs/c-semantics-design.md` §3.1): `unsupported` retires by climbing
a rung, `ub` **never retires because it is the product**, `libc`
retires by widening the slice. The SV mapping:

| cause | SV instance | retires by |
| --- | --- | --- |
| `unsupported` | out-of-tier construct (`initial`, `#`, classes, `Unsupported` nodes in the envelope) | climbing a rung |
| **`nondeterminism`** | **race: two legal schedules, two observable traces** | **NEVER — it is the product** |
| `x-propagation` | unknown value reaching an observable | never — it is a *value*, not a fault (§3) |
| `libc`-analogue | unmodelled system task (`$display`, `$random`, DPI import) | widening the slice / axiomatic boundary |
| `timeout` | comb loop, fuel exhaustion | genuine defect class, already implemented |

**The J.1-analogue, and the ruling.** C's Annex J enumerates
unspecified and undefined behaviours; SV's counterpart is not one annex
but three distinct kinds of latitude, and **they must not be pooled**:

1. **Scheduling nondeterminism** (clause 4) — the standard *grants* the
   implementation freedom. Analogous to C's **unspecified** behaviour.
2. **X-propagation** (clauses 6, 11) — *fully specified*, per-operator,
   deterministic. **Not latitude at all**, and the most common mistake
   would be to model it as such.
3. **True undefined/illegal cases** — e.g. multiple continuous drivers
   on a variable; the standard says the result is an error, not a
   value. Analogous to C's **undefined**.

Thomas's **∀-resolution ruling for unspecified behaviour generalises
directly to (1), and the SV lane is where it is already load-bearing.**
The C tier's form (`docs/c-semantics-design.md` §4.4) is *execute a
canonical order, and REFUSE where a static census cannot show the order
unobservable*. The SV form is stronger and already shipped:

```
m ⊨ P   ≡   ∀ stim σ tr, m / stim ⇓[σ] tr → P stim tr
Sv.Deterministic m — all schedules give the same observable trace
```

**Every SV theorem is already universally quantified over the schedule
oracle.** The tier does not pick a canonical order and apologise; it
proves the property *for all legal orders*, and race-freedom is a
theorem (`Sv.Deterministic`) rather than an assumption. `σ_src`
(declaration order) exists only as the *executable* default for
differential testing, and the harness demonstrably tries others —
`race_blk_one_edge` matched `sigma_rev` in today's run.

**So the ruling generalises thus: where C refuses what it cannot show
unobservable, SV proves over the whole space.** SV can afford the
stronger form because its nondeterminism is *coarse and enumerable*
(a permutation of ready processes at a scheduling point), where C's
unsequenced-modification space is tangled with aliasing. The C tier's
refusal is the weaker fallback for a harder problem — **not a different
philosophy**, and the charter records that the two lanes should not be
"harmonised" into the weaker one.

### 2.5 The verification tier is a SEPARATE tier

Clauses 8, 13, 15, 18, 19, 24 — classes, constrained randomisation,
functional coverage, mailboxes, programs — are **half the public
suite's mass** (`uvm` is the single most common tag at 105 occurrences,
`chapter-18` is the largest chapter at 134 tests) and share almost
nothing with the simulation semantics. They need an object model, a
constraint solver, and a randomisation oracle.

**The charter's position: this is a distinct tier with its own
milestone ladder, and conflating it with the simulation semantics
would misprice both.** The existing `docs/sv-spec-surface.md` gallery
already anticipates this (examples 8, 17, 18 are explicitly
design-target). A tier that models clauses 4/6/7/9/10/11/12 well and
refuses clause 18 loudly is a *coherent* product; one that half-models
both is not.

---

## 3 FOUR-STATE LOGIC — the value model, priced

### 3.1 What the value model must be, and it is already built

C's value model is fixed-width two's-complement integers over 11 scalar
types, and the census forced a split (unsigned wraps, signed refuses).
**SV's is not integers at all**, and the difference is the single
largest semantic gap between the two tiers.

Already normative in `docs/sv-design-m0.md` and implemented:

```
inductive Logic | l0 | l1 | lx | lz
structure LVec where bits : Array Logic     -- LSB-first
LVec.known? : LVec → Option (BitVec w)
```

**A 4-state vector is not a number.** `LVec.known?` is the *partial*
bridge to `BitVec`, and its partiality is the whole design: a value may
be *unknown at some bit positions*, and that is an ordinary,
fully-specified state, not an error.

### 3.2 X-propagation is specified, per-operator, and NOT uniform

The facts below were verified against Xcelium when M0 was built, and
they are the reason a naive "any x → x" rule is wrong:

* **Arithmetic** (`+ - * < <= >=`): any x/z bit in *either* operand
  collapses the *entire* result to x (whole-vector, clause 11.4.3).
  Never bit-precise carry.
* **Bitwise**: per-bit tables, and they are *not* strict — `0 & x = 0`,
  `1 | x = 1`. Information survives.
* **Logical `==`**: 0 if any position has both bits known and unequal;
  else x if any x/z; else 1. **Not** "any x → x".
* **Case `===`**: exact 4-state match, *always* returns 0 or 1 — the
  designated escape hatch from x.
* **`if (c)`**: true iff `c` has at least one `l1` bit; x/z-only takes
  the else branch, and an `if` with no else **holds** its target rather
  than poisoning it.
* **Ternary `c ? a : b`** with unknown `c`: evaluate both, bitwise
  merge, agreeing bits survive (clause 11.4.11) — **different from
  `if`**, and a classic source of confusion.

**Three operators are non-monotone in the information order** (`&`,
`|`, `===`), which means x-propagation **cannot** be implemented as a
generic lifting of a two-state semantics. It must be tabulated
per-operator. That is the concrete price of the value model, and it is
already paid in `LeanModels/Sv/Basic.lean`.

### 3.3 X-pessimism, and what it means for MATCH verdicts

**This is the value model's sharpest consequence for differential
testing.** Real simulators are *pessimistic* about x in some places and
*optimistic* in others, and the standard permits some of this
divergence.

* **X-pessimism**: the model yields x where a real design would settle
  to a definite value (e.g. `(a & ~a)` computed bit-blind on an unknown
  `a` gives x, though it is 0 for any concrete `a`).
* **X-optimism**: a simulator yields a definite value where the true
  set of possible behaviours is not a singleton — famously `if (x)`
  taking the else branch, which *hides* a real design bug.

The tier models the **LRM's** rules, which include the optimistic
`if`. `docs/sv-spec-surface.md` §5 already frames this as *"we model
the LRM, and prove it honestly"*.

**The verdict rule this forces, and the charter states it plainly:**

> A differential MATCH against a simulator is a check on the *model*,
> **not** a proof about the *design*. Where a trace contains x, the
> honest reading of MATCH is *"our model reproduces the LRM's
> x-behaviour, which the simulator also implements"* — never *"the
> design is correct."*

Concretely: of today's 10 green harness cases, **three are explicitly
x-carrying** (`adder_x`, `counter_xrst`, `xsel_x`) plus
`toggle_x`. Those four are the model's x-rules agreeing with Icarus's
— genuinely valuable, and *not* statements about the designs. The
sharper theorems are the x-free ones: `counter_refines` (cycle
refinement against a golden Lean model) and `swap_nba_det`
(`Sv.Deterministic`).

**Consequence for the corpus.** A conformance corpus scored purely on
MATCH will over-report. The refusal taxonomy (§2.4) must keep
`x-propagation` **out of** the fault classes — an x in a trace is a
value, and a test whose expected output is x is a *passing* test, not a
degraded one.

---

## 4 DRIVER-ARTIFACT CENSUS

The C tier's driver is `tools/ctwin/sunfish.c`, a node-identical twin
of the Python corpus — which is what makes the square (A ≡ C) even
statable. **The charter's finding: SV has no ctwin-analogue, and it
does not need one — but it does need a designated driver, and today it
has three de-facto ones that were never chosen.**

### 4.1 What is already driving the lane

| artefact | provenance | licence | role today |
| --- | --- | --- | --- |
| 6 hand-written designs (`adder`, `counter`, `race_blk`, `swap_nba`, `toggle`, `xsel`) | written for this repo | repo's own | the M0 gallery; all six proved |
| 7 `t2_*` probes | written for this repo | repo's own | per-feature `sv-0.2` probes |
| 5 CV32E40P modules (`popcnt`, `ff_one`, `alu_div`, `fifo`, `register_file_ff`) | **OpenHW Group**, pinned `6033d2b1…` | **Solderpad 0.51 / Apache-2.0** | the real-RTL acceptance set |

The CV32E40P modules are the closest thing to a real driver: genuine
industrial RISC-V RTL, dual-simulator validated. **But they are
someone else's IP**, vendored as individual `.sv` files into
`Examples/system-verilog/sem2/` while their build dependencies
(`cv32e40p_pkg.sv`) are deliberately *not* vendored — which is why one
of the 18 envelopes cannot regenerate here (§0). Solderpad/Apache is
permissive, so this is a *completeness* wart, not a licensing one.

### 4.2 Thomas's own SV, surveyed read-only

Surveyed across `~/repos`; **nothing chosen**, candidates ranked.

| repo | `.sv/.v` files | remote | licence | note |
| --- | ---: | --- | --- | --- |
| **`DRAM_uvm`** | **11** | **`thomasahle/DRAM_uvm`** | none | **Thomas's own**, 11 of 12 commits his; 805 lines total |
| `sv-tutorial` | 58 792 | `thomasnormal/sv-tutorial` | none | huge; course material + deps |
| `UVMCourse` | 224 | `thomasnormal/UVMCourse` | none | course exercises |
| `verification` / `verification2` | 13 164 / 1 642 | `normal-computing/verification` | none | **employer-internal** |
| `axi4_avip` | 348 | `mbits-mirafra/axi4_avip` | LICENSE.md | third-party AVIP |
| `verilator-verification` | 3 690 | `antmicro/…` | LICENSE | third-party |
| `eda`, `dv-smith`, `cvdp_benchmark` | 0–2 | — | — | not SV corpora |

**Ranked shortlist for a designated driver:**

1. **`DRAM_uvm/design.sv` — the standout.** 98 lines containing
   `DRAM_model`, plus `interface.sv` (21 lines). Thomas's own, on his
   *personal* GitHub (no employer entanglement), small enough to
   ingest whole, and a real clocked design with memory. Its 9-file UVM
   testbench half is **far** out of tier (clause 8/18) and would be
   ignored — which is clean, not awkward: the design and its testbench
   are separate files.
2. **The existing 6 M0 designs, promoted.** They already round-trip,
   are already proved, and are unencumbered. The honest objection: they
   were written *to be easy*, so they cannot demonstrate the tier
   scaling.
3. **CV32E40P, expanded.** Best fidelity-per-effort for *real* RTL, but
   third-party and needs the external checkout pinned properly.

**No repo contains a "twin" in the ctwin sense** — an SV design that is
a transcription of something the repository already models in another
language. The C tier's square is not reproducible here, and the charter
recommends the owner **not** try to manufacture one: SV's differential
oracle is a *simulator* (already wired: Icarus green today, Xcelium
historically), which is a stronger and more standard oracle than a
hand-maintained twin.

---

## 5 CONFORMANCE CORPUS — the recommendation

Per the family law, **fetch-don't-vendor unless licences clearly
permit**. The two candidates split cleanly:

| | vendor? | why |
| --- | --- | --- |
| `sv-tests` `tests/**` | **yes — permitted** | uniform ISC, per-file SPDX, single holder, 0 contamination hits |
| `sv-tests` `third_party/**`, `tests/generated/**` | **never** | reaches GPL-2.0 (ivtest), Solderpad, unlabelled 2 504-file core |
| `sv-tests-2` | **never** | no licence at all; employer-internal; embeds the IEEE PDF |

**Recommendation, for the owner to accept or reject.** Vendor a
*pinned subset* of `sv-tests/tests/**` under a `PROVENANCE.md` carrying
the ISC text and the commit sha `4f24807…` — the same pattern
`vendor/cpython-3.9-lib-test/` already uses — and keep `sv-tests-2` as
a **fetch-only, path-configurable** corpus for the owner's private
measurement. Concretely that means `census.py`'s hard-coded
`DEFAULT_CORPUS` (§1.3) becomes a required flag or an env var, so the
instrument is honest on any host.

**Other free corpora**, noted and not pursued: Icarus's `ivtest`
(**GPL-2.0 — unusable for vendoring**), Yosys's `tests/` (ISC),
Verilator's own regression suite (its test files are largely
permissive but the harness is LGPL-3/Artistic; Verilator's suite is
*also* a genuine corpus and worth a later look). **Commercial suites
(Accellera/UVM golden, vendor conformance kits) are out of scope: no
purchases, and the charter proposes none.**

---

## 6 THE ENDGAME MENU — priced, not chosen

The owner has named a flagship: **prove that an SV circuit computes
IEEE 754 division correctly.** The shape is the verified-FPU tradition
placed inside this family's pattern — the SV semantics runs the circuit
at bit level, a shared SoftFloat component's *spec* layer says what the
output bits must be (`op_correct` = the correctly-rounded exact
rational result, decidable, no reals), and the correctness theorem is
the bridge between them.

This section prices that honestly, and censuses the one existing
artifact that might have been a foothold.

### 6.1 `LeanModels/Circuit/` — censused, and it is NOT the foothold

Measured: **25 files, 4 309 lines**. What it models, read from the
sources:

| module | subject |
| --- | --- |
| `Nature.lean` | physical dimensions as integer exponents of the **seven SI base units** |
| `Discipline.lean` | conservative vs signal ports; potential/flow, KCL-style conservation |
| `Behavior.lean` | the semantic root: an **acausal relation**, deliberately not functional |
| `DC / AC / Transient / RobustDC` | the analysis interpretations |
| `Contract / Enclosure / Assurance` | compositional port contracts, interval enclosures |
| `Spice / Surface / ParserRunner` | `load_circuit` — parses SPICE **in Lean** |

**This is the ANALOG tier.** Its carriers are `Rat`/`Real`/`Complex`,
its ports conserve signed flow, and its whole design goal is to keep
the numeric carrier an *interpretation parameter* so DC, transient and
AC analyses can differ. It is the partner of `LeanModels/Spice/`
(23 366 lines) and `LeanModels/VerilogA/` (606) — continuous-domain
circuit theory, Verilog-AMS's natures and disciplines made precise.

**It is therefore not a foothold for a bit-level divider proof, and the
charter says so plainly rather than stretching a resemblance.** An
IEEE 754 divider correctness theorem is a statement about *finite
vectors of bits* under Boolean operations. `Circuit/` has no bit, no
`BitVec`, no Boolean gate; `Sv/` has `Logic`, `LVec` and
`LVec.known? : LVec → Option (BitVec w)`. **The digital foothold is the
SV tier itself**, which is the reassuring answer: the flagship needs
the tier this charter is founding, not a different one.

Two honest qualifications. (a) `Circuit/` remains the right home if the
question ever becomes *"does this transistor-level divider settle to
the right voltages"* — a genuinely different and much harder claim, and
not the one the owner named. (b) `Circuit/` is a **live demonstration
that this repository can carry a large, Mathlib-backed, non-Python
semantic tier to a real proof surface**, which is evidence about
feasibility even though none of its code transfers.

### 6.2 The minimal sufficient 1800 fragment — and most of it EXISTS

The C tier's rung 0 was "the 45 node kinds ctwin actually uses". The
analogue here: **which slice of IEEE 1800 does a divider proof actually
need?** The answer is much less than the language, and — the charter's
best news — **much less than the full scheduler.**

A combinational or pipelined arithmetic datapath needs:

| clause | what is needed | status in the tier |
| --- | --- | --- |
| 6, 7 | packed vectors, `logic`, parameters, packed structs | **have** (`LVec`, `sv-0.2` binders) |
| 11 | operators: arithmetic, bitwise, shift, compare, concat, ternary, part-select | **have** |
| 10 | continuous assignment (`assign`) | **have** |
| 12 | `if`/`case`/`for` inside procedural blocks | **have** |
| 9 | `always_comb`; `always_ff @(posedge)` if pipelined | **have** |
| 23, 27 | module instantiation, hierarchy, `generate` loops | **have** (generate unrolls structurally; `popcnt`'s four levels → 31 processes) |
| **4** | **comb settle to fixpoint; for pipelined, the NBA split** | **have — at cycle granularity** |

**Clause 4's full region ladder is NOT required.** A combinational
divider needs only the Active-region fixpoint; a pipelined one needs
the Active/NBA split the cycle model already implements. `initial`,
`#` delays, Inactive, Observed/Reactive and Postponed — the expensive
half of §2.3 — **are all testbench concerns, and a datapath proof
touches none of them.** Likewise clause 8/18's verification tier is
entirely out of scope. **The flagship does not depend on either of the
two largest open scoping questions in §8**, which is what makes it a
credible endgame rather than a wish.

**The evidence that the fragment is real: a divider is ALREADY
INGESTED.** `Examples/system-verilog/sem2/alu_div/cv32e40p_alu_div.sv`
— CV32E40P's *"Simple Serial Divider … for signed integers (int32)"*,
226 lines — round-trips byte-identically today (§0) at schema
`sv-0.2`. It is a clocked, real, industrial divider already inside the
tier's vocabulary. **It is an integer divider, not a floating-point
one**, and the charter will not blur that.

### 6.3 The ladder, priced in three rungs

**Rung A — the integer divider, as the warm-up.** Prove
`cv32e40p_alu_div` computes signed 32-bit quotient/remainder. The SV
side is *already done*: ingested, in-tier, dual-sim validated. What is
missing is a Lean spec (`Int` division with the RISC-V rounding and
divide-by-zero conventions) and the bridge theorem over the divider's
serial cycle count. **This is the cheapest real theorem available to
the tier and it needs no new semantics** — its difficulty is the
induction over serial iterations, not the language.

**Rung B — IEEE 754 division, the flagship.** Two prerequisites, and
neither is SV work:

1. **The spec layer.** `op_correct` = round-to-nearest-even of the
   exact rational quotient. Decidable over `Rat`, no `Real` needed —
   which is what makes it a `#guard`-able, `decide`-able specification
   rather than an analysis. **Censused: nothing of the kind exists in
   this repository today** (`git ls-files` for softfloat/ieee754/float
   returns only `Spice/DiffPair.lean` and a SPICE fixture, both
   unrelated). It is being commissioned via the architecture lane, and
   **rung B is gated on it**.
2. **The RTL.** No FP divider is vendored here. **But Berkeley
   HardFloat is already on this machine**, at
   `sv-tests/third_party/cores/black-parrot/external/HardFloat`: 44
   `.v` files including `divSqrtRecFN.v`, `divSqrtRecFN_small.v`,
   `divSqrtRecFN_medium.v`, plus a `divSqrtRecFN_small_spec.v`. Its
   `COPYING.txt` is the Berkeley HardFloat Release 1 licence (BSD-3
   style) and states it applies *to the whole release as well as to
   each source file individually* — **a clean per-file grant**, which
   is exactly what the family law wants and what `sv-tests`'s other
   `third_party` entries lack.

   **A pleasing alignment worth recording:** HardFloat's author, John
   Hauser, also wrote Berkeley **SoftFloat** — so the spec layer being
   commissioned and the RTL being verified descend from the same
   reference. That is a strong pairing.

   **One honest obstacle, named now rather than discovered later:**
   HardFloat computes in a *recoded* internal format (`recFN`), not raw
   IEEE 754 bit patterns, with `fNToRecFN`/`recFNToFN` at the
   boundaries. The correctness theorem must therefore compose through
   the recoding, which is extra proof surface and a place where a
   sloppy statement would prove the wrong thing. It is also **Verilog,
   not SystemVerilog** — inside the tier's fragment, but the extractor
   has only ever been run on `.sv`.

**Rung C — the general completeness ladder.** Climb the clause coverage
of §1.5's dictionary corpus-wide. Buys the broadest surface and no
flagship theorem. Listed for completeness; the charter observes that A
and B are *narrow and deep* while C is *wide and shallow*, and that the
owner has already indicated which he values.

**What all three share** is SV-M1 (§7): a pinned frontend, a corpus
that resolves, a committed census artifact, and a round-trip gate.
**None of the endgames needs to be chosen to start**, and the choice
becomes load-bearing only after M1 — the same structure §L35 found for
C.

---

## 7 THE FIRST MILESTONE — SV-M1

**The M1-analogue the dispatch asked for — "a pinned SV source ingested
via a real frontend to an envelope schema, round-tripped with
census-anchored `#guards`" — is ALREADY DONE, twice.** Schema `sv-0.1`
(concrete) and `sv-0.2` (symbolic) both exist, 17 of 18 envelopes
regenerate byte-identically today (§0), and `Examples/system-verilog/`
carries ingested designs with load-time cross-checks
(`PDesign.crossCheck` refuses a load on mismatch).

**Re-doing it would be re-work.** The charter therefore proposes the
milestone that the census says is actually next, and it is a
*consolidation* milestone — because a tier that is green but
unreproducible is one bad afternoon from being neither.

### SV-M1: THE LANE IS REPRODUCIBLE FROM A CLEAN CHECKOUT

Eight inches, each closing a defect this census actually found.

1. **Pin the frontend.** `pyslang==11.0.0` recorded as a declared
   dependency with the `python3.12` requirement, so §1.1's
   `ModuleNotFoundError` cannot recur silently. *Closes §1.1.*

2. **Un-hard-code the corpus path.** `census.py`'s `DEFAULT_CORPUS`
   becomes a required `--corpus` (or env var) that **refuses loudly**
   when unset or absent — never a silent default to a path that does
   not exist. *Closes §1.3.*

3. **Land the missing census artefact.** Re-run the instrument and
   commit `census.json`, with a `--compare` mode on the C tier's model
   so corpus staleness is **mechanically detectable**. *Closes §1.2.*

4. **Decide and record the anchor corpus** (owner's call, §8) and make
   `docs/sv-corpus-coverage.md` state which corpus, which commit,
   which licence — the memo currently names none of the three.

5. **A round-trip gate that runs in CI.** Today's 17/18 check was run
   *by hand by this charter*. It should be a `maybe`-gated script:
   regenerate every committed envelope, diff, fail on drift. This is
   the SV analogue of `--compare`, and it is cheap because the
   envelopes and sources are both in-tree. *Guards §0's finding.*

6. **Designate the driver artefact** (owner's call, §8) and, if
   `DRAM_uvm` is chosen, ingest `design.sv` + `interface.sv` to an
   envelope with `#guard`s anchored on facts the census independently
   knows — module count, port count, process count.

7. **Move the instrument to `harness/`.**
   `extractors/sv/census.py` → `harness/sv_construct_census.py`, per
   `docs/family-architecture.md`'s rule that *extractors extract,
   instruments measure*. The family doc names this as the one standing
   exception, to be fixed when this lane next opened. It has.

8. **Contain the frontend crash.** Per-file subprocess isolation in the
   census so a SIGTRAP becomes a recorded `error` row with a file name,
   never a silent hang (§1.6) — and an upstream report to slang for
   `` `unconnected_drive pull2 ``. **This is the inch that makes the
   anchor-corpus decision free to take either way.**

**What SV-M1 deliberately does NOT do:** no new semantics, no clause-4
region ladder, no verification tier, no new proofs. It makes the
existing 8 166 lines *reproducible and defensible*, which is the
precondition for every larger choice in §8.

---

## 8 STILL OWED BY THE OWNER

The charter recommends nothing in this section. Six decisions, in
dependency order.

1. **THE ANCHOR CORPUS — blocks SV-M1 inches 3–4, and it is the one
   with a licence consequence.** `sv-tests-2` is 21× larger, spans
   clauses 3–40, and is the better instrument — but it is inside
   `normal-computing/mox`, carries **no licence**, and embeds the IEEE
   1800-2023 PDF. The public `sv-tests` is ISC-clean and vendorable but
   1 028 tests over clauses 5–26. Options: (a) switch the public claims
   to `sv-tests`, keep `sv-tests-2` private and path-configured;
   (b) keep `sv-tests-2` as the anchor and accept that no outside
   reader can reproduce a coverage number; (c) both, with the public
   suite as the *published* claim and `sv-tests-2` as an internal
   supplement. **Whether `sv-tests-2` may be cited at all in a public
   repository is a question only the owner can answer**, and the
   coverage memo already cites it.

2. **THE DRIVER ARTEFACT.** Designate one, per §4: `DRAM_uvm`'s
   `design.sv` (Thomas's own, personal account, 98 lines), the existing
   M0 six promoted, or CV32E40P expanded with its `pkg` dependency
   pinned. **Or rule that the lane needs no single driver** because its
   oracle is a simulator — which is a defensible answer the C tier
   could not have given.

3. **THE SCOPE BOUNDARY: is the verification tier (clauses 8, 18, 19,
   24) in or out?** §2.5 argues it is a separate tier; the owner
   decides whether the SV lane's remit is *simulation semantics* or
   *the whole language*. This is the single largest scoping question
   and it changes every downstream estimate.

4. **THE CLAUSE-4 LADDER: does the tier go past the cycle collapse?**
   Full region semantics (Inactive, Observed, Reactive, Postponed)
   unlocks `initial`, `#` delays, clocking blocks and program blocks —
   and **re-opens every existing theorem**, because the trace type
   changes. Priced in §2.3 as its own milestone. Not needed for
   synthesisable RTL; required for testbench semantics.

5. **THE SPEC EDITION.** -2023 (the corpus's target) or -2017 (what
   `sv-design-m0.md` cites)? They mostly agree, but the lane currently
   mixes them. §2.1's rule — cite the edition you measured — holds
   either way, but the *reference* edition should be named once.

6. **WHICH ENDGAME (§6)** — and specifically whether **rung A**, the
   integer divider, is worth taking as a warm-up. It is unusually
   cheap: the RTL is already ingested and in-tier, so the only new work
   is a Lean spec and the bridge. It would be the tier's **first real
   correctness theorem about a real industrial module**, and it
   de-risks rung B's proof architecture before the SoftFloat spec layer
   arrives. The counter-argument is that it proves nothing about
   floating point, which is what the owner actually named.

**A standing obligation, recorded.** The Xcelium results that make
`docs/sv-design-m0.md`'s 4-state table "normative — verified on
Xcelium" were taken on a host this charter cannot reach. Icarus
reproduces the 10 harness cases today, but the *operator-level* table
has not been re-verified here. It should not be called
dual-simulator-verified in any new claim without a re-run.

---

## 9 WHAT LANDED WITH THIS CHARTER

This document and a backlog section. **No Lean, no code, no existing
file changed** — the C charter's rule, kept.

**Every headline is a run made today**, not a citation: the harness
(10/10 green vs Icarus 12.0), the round-trip (17/18 byte-identical,
1 absent-input), the build (3 690/3 693 jobs, zero compilation errors,
all 14 `LeanModels.Sv.*` built, two Python-tier targets SIGTERMed under
contention), the proof
hygiene (86 theorems, 0 `sorry`, 0 `native_decide`), the frontend gap
(`ModuleNotFoundError`, fixed by a venv in under a minute), the missing
`census.json`, the non-existent `DEFAULT_CORPUS` path, the
corpus-disjointness (0 of 11 `unlockable.txt` files present upstream),
the licence censuses of both corpora, the re-census of the public suite
through the committed instrument — **which found a SIGTRAP crash in
pyslang on a two-line negative test, and a `Pool` deadlock that turns
that crash into a silent hang** — the census of `LeanModels/Circuit/`
that rules it out as the flagship's foothold, and the location of
Berkeley HardFloat's `divSqrtRecFN` under a per-file BSD-3 grant.

**Two corrections the charter made to itself**, both kept visible
because the family law says instrument faults are findings. (1) The
first round-trip run reported 12 failures that were the *charter's*
invocation error, not the tree's defect — *read the mode out of the
artefact*. (2) §1.6 began life asserting that switching the anchor
corpus was *"a licensing decision, not an engineering one"*; running
the instrument refuted it. **Neither was visible without executing the
thing**, which is the entire argument for census-first.
