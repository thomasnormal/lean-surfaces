# The SystemVerilog tier: FOUNDING CHARTER

**Status: the workstream's founding document.** The owner chartered the
language-family programme with *"System Verilog also has a spec, that we
can similarly follow"* — versioned surfaces, spec-mirror as the general
behaviour — and this charter founds the SV lane on the C tier's proven
template (`docs/c-tier-charter.md`, §L35): census first, corpus and
licence surveyed per-file, taxonomy mapped, first milestone planned.
**No Lean semantics in this pass. No existing file changed** by the
charter itself; the consolidation commit that followed it is listed in
§10.

**It presented six decisions and recommended none. The owner ruled all
six the same day** — §6 records them verbatim, §8 re-cuts the ladder
around them, and §9 lists the one thing still outstanding, which is an
access rather than a decision.

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

2. **The extractor still round-trips BYTE-IDENTICALLY — 18 of 18.**
   Re-running `extractors/sv/extract.py` over every pinned source in
   `Examples/system-verilog/` and diffing against the committed
   envelopes: **18 identical, 0 differing, 0 errors.** Six are schema
   `sv-0.1` (single-file), twelve are `sv-0.2` (symbolic `--top`).

   **This paragraph first published "17 of 18", and that was wrong
   twice over** — wrong in the count and wrong in the cause. The
   holdout, `cv32e40p_register_file_ff`, was blamed on a missing
   `cv32e40p_pkg.sv` from the un-vendored OpenHW checkout. In fact the
   file `cv32e40p_register_file_ff.sv` declares module
   `cv32e40p_register_file` — filename and module name differ, as they
   do across all three of OpenHW's register-file variants — so a
   `--top` derived from the *filename* could not resolve it. Read from
   the envelope's own `top` field it regenerates byte-identically **and
   needs no external checkout at all**. A plausible, unverified
   diagnosis survived a whole publication; `harness/sv_round_trip.py`
   now runs this check so the next one cannot.

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

**A methodological note that belongs in the charter because it twice
became a false finding.** The first round-trip run reported *12
differing*. That was the instrument, not the tree: the `sem2` envelopes
are `sv-0.2`, which requires `--top <module>`, and the loop had invoked
single-file mode. Re-run with the mode each envelope declares in its own
`schema_version` field, the differences vanished entirely. **An envelope
compared against the wrong extraction mode is a silent wrong answer of
exactly the C charter's kind**, and the rule it yields is now written
down: *read the mode out of the artefact, never assume it.*

The rule has **three** edges, and each was found by tripping over it:
the **schema** (`sv-0.1` vs `sv-0.2`), the **top module** (from the
envelope's `top`, never the filename — item 2 above), and the **source
path spelling**, because the recorded path is *part of the envelope*:
regenerating with absolute paths where the envelope recorded
repo-relative ones made all 18 differ, by exactly the string-length
delta. The gate now mirrors the recorded layout in a scratch directory
and runs there.

---

## 1 THE CENSUS — and the four defects it found

### 1.1 The frontend is `pyslang`, and it is NOT installed — **CLOSED**

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

### 1.2 The corpus census cites an artefact that is NOT in the tree — **CLOSED**

`docs/sv-corpus-coverage.md` states its machine-readable results live
at `harness/sv/conformance/census.json`. Measured:

```
$ git ls-files harness/sv/conformance/
harness/sv/conformance/runner.lean
harness/sv/conformance/unlockable.txt
```

**`census.json` is not tracked and not present** — and the reason is
worse than an oversight: `.gitignore:5` lists
`harness/sv/conformance/census.json`, so the document cites an artefact
its own repository is configured to exclude. It was not forgotten; it
was **excluded by rule**, which looks deliberate and so invites nobody
to fix it.

**CLOSED.** The per-file records are 11.9 MB across 21 186 files, far
outside this repository's census range (6 KB - 773 KB in `docs/`), so
they stay regenerable-but-uncommitted while the half every claim
actually cites — provenance + summary, 20 KB, sorted — lands as
`docs/sv-construct-census.json`, with a `--compare` mode that exits
non-zero on drift. The document's
headline numbers — 21 336 files walked, the construct-frequency table
that it calls *"THE IMPLEMENTATION PRIORITY QUEUE"*, the per-chapter
coverage — are therefore **unreproducible from this repository**: the
aggregates survive only as prose in the memo that cites the missing
file. The sibling `unlockable.txt` (11 lines) did land, which is how
§1.4 below could be measured at all.

### 1.3 The census instrument points at a path that does not exist — **CLOSED**

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

**CLOSED.** The hard-coded path is replaced by a registry resolved by
`--corpus-name`, which tries candidate locations in order and
**REFUSES** with every path it tried when none exists (exit 2). Both
corpora are registered, so ruling §6.1's anchor is a flag rather than a
project. And the missing staleness check now exists: `--compare` reports
every drifting key against the committed summary. Verified — a
perturbed artefact is caught and exits 1; an unperturbed one reports
`compare: IDENTICAL (21186 files, corpus sv-tests-2)`; two consecutive
runs are byte-identical, once `elapsed_seconds` was removed from the
artefact for being a fact about the afternoon rather than the corpus.

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

**And one correction this charter owed the family doc — now
RESOLVED BY RULING.** The registry row's corpus field reads
**`sv-tests-2`**, which §1.4 measures as employer-internal, carrying
**no licence**, and embedding the IEEE PDF; the charter objected that a
public repository's registry should not name a corpus its readers
cannot obtain. **Ruling §6.1 settles it:** `sv-tests-2` is citable
internally, open-sourcing is deferred, and the standing condition is
that it **stays out of public artifacts** until a further ruling. So the
row stands for internal purposes, and the registry's *public*
presentation is what remains gated. The IEEE PDF stays unopened
regardless — that is our own law, not a consequence of the licence
question.

**A second correction, still owed OUTWARD and not resolved by any
ruling** (§7.3): the family document records `Run σ α` as used by
*"Python (16 files) and SystemVerilog (3)"*. SV's true count is
**zero** — it uses its own `Sv.Res`, and the "3" is a bare-word match on
doc comments. The move-to-`Core` trigger is fixed on the premise that SV
is a second consumer, and it is not.

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
**per-design obligation that is discharged or refuted, never assumed**.

> **CORRECTION (2026-08-22), because the sentence this replaces
> overclaimed.** It read *"race-freedom is a theorem (`Sv.Deterministic`)
> rather than an assumption"*, which invites the reading that the tier
> establishes race-freedom. **It does not, and cannot: IEEE 1800 leaves
> same-region ordering unspecified, so a racy design genuinely has no
> single outcome.** `Deterministic (d : Design) : Prop` is a
> **design-indexed predicate**, not a law — and the tier proves it for
> five designs (`adder_det`, `xsel_det`, `swap_nba_det`, `toggle_det`,
> `counter_det`) and proves its **negation** for the sixth:
> `race_blk_not_deterministic : ¬ Deterministic raceBlkDesign`.
>
> **The Lean was never wrong** — audited, no `∀ d, Deterministic d`
> exists and no proof consumes an unrestricted form. The defect was in
> this document's wording.
>
> One refinement on how the correction should be phrased: in this tier
> `Deterministic d` **IS** race-freedom — the same predicate, "all legal
> schedules agree on the trace". So the fix is *not* to write
> `RaceFree d → Deterministic d`, which would be a tautology here; it is
> that the predicate is a **premise or a per-design theorem, never a
> tier-wide conclusion**. `σ_src`
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

### 2.5 The verification tier — proposed as separate, **RULED IN**

Clauses 8, 13, 15, 18, 19, 24 — classes, constrained randomisation,
functional coverage, mailboxes, programs — are **half the public
suite's mass** (`uvm` is the single most common tag at 105 occurrences,
`chapter-18` is the largest chapter at 134 tests) and share almost
nothing with the simulation semantics. They need an object model, a
constraint solver, and a randomisation oracle.

**The charter proposed** that this be a distinct tier with its own
ladder, on the argument that a tier which models clauses 4/6/7/9/10/11/12
well and refuses clause 18 loudly is a *coherent* product where one that
half-models both is not.

**RULED OTHERWISE (§6.3): everything is in scope, one lane, one
ladder.** The argument above is not thereby refuted — it is answered by
sequencing instead of by separation. §8.3 puts the verification tier at
**R2 and later, after the scheduler**, precisely because clauses 8/18/19
need a clock and a process model to hang on, and R1 is what supplies
them. "Refuses clause 18 loudly" remains the correct *interim* state;
it is now a rung rather than a boundary.

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

## 4 DRIVER-ARTIFACT CENSUS — **DISSOLVED by ruling §6.2**

> The census below stands as measurement; its *question* was answered by
> dissolving it. With full-spec support as the endgame, **the
> conformance suite is the fixture set** and no dedicated driver is
> wanted. `DRAM_uvm` is recorded as an optional showcase. The section's
> own conclusion — that SV has no ctwin-analogue and does not need one,
> because its oracle is a simulator — is upheld.

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

## 5 CONFORMANCE CORPUS — the recommendation, and how it was **RULED**

> **Ruling §6.1 took the other branch from the one this section leans
> toward, and did so knowingly.** `sv-tests-2` is citable for internal
> docs and proofs; open-sourcing is deferred; it stays out of *public*
> artifacts meanwhile. The per-file licence work below is therefore not
> wasted — it is what makes the public/internal split enforceable, and
> it is what the vendoring rule (`tests/**` only) still governs the
> moment anything is vendored. The IEEE PDF stays unopened either way.

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
## 6 THE RULINGS — all six taken, 2026-08-22

The charter presented six decisions and recommended none. **The owner
ruled all six the same day.** They are recorded here verbatim, each with
what it changes.

### 6.1 The anchor corpus — `sv-tests-2` IS citable

> *"sv-tests-2 IS CITABLE (open-sourcing deferred — so: internal
> docs/proofs may cite it freely; keep it out of PUBLIC artifacts until
> he rules; the embedded IEEE PDF stays unopened per our own law
> regardless)."*

So `docs/sv-corpus-coverage.md` keeps its anchor and its numbers stand.
Three standing conditions: internal citation is free; **public
artifacts must not name it** until a further ruling; and the embedded
`ieee-1800-2023.pdf` **stays unopened**, which is our own law and not
contingent on the licence question.

**What landed under this ruling.** `extractors/sv/census.py` keeps
`sv-tests-2` as its default corpus — but by *name* through a registry,
never by a hard-coded absolute path, and the public suite is wired
beside it so the anchor is a flag. §8.1's decision-neutral half is
therefore already done: switching is `--corpus-name sv-tests`.

### 6.2 The driver artefact — DISSOLVED

> *"Driver artifact: DISSOLVED by ruling 6 — no dedicated driver; suite
> tests are the rung fixtures; DRAM_uvm noted as optional showcase
> only."*

The charter's §4 conclusion is upheld and then made moot: with full-spec
support as the endgame, **the conformance suite IS the fixture set**.
There is no ctwin-analogue and none is wanted. `DRAM_uvm` survives as an
optional showcase, not a dependency.

### 6.3 Scope — EVERYTHING, with a PLUGGABLE oracle

> *"EVERYTHING IN SCOPE — the whole spec including the verification tier
> (classes/constrained-random/assertions). New oracle policy: XCELIUM
> where Icarus falls short."*

This reverses the charter's §2.5 suggestion that the verification tier
be a separate lane. It is one lane and one ladder.

The ruling carries a design order with it: **the oracle becomes a
parameter from day one**, with *per-test oracle attribution recorded* —
which oracle produced each expected result is **provenance**, exactly as
the C tier names the interpreter on its coverage lines. Icarus stays the
default; Xcelium is used where Icarus falls short; **access details are
owed by Thomas (§9), and the design must not block on them.**

This is the same lesson the census just paid for in cash: an artifact
that does not record what produced it cannot be checked later. The
census now stamps corpus, frontend family, platform and walk mode for
precisely this reason, and the harness must stamp its oracle for the
same one.

### 6.4 Clause 4 — the FULL scheduler, and EARLY

> *"Clause-4: FULL scheduler in scope, sequenced as rungs — cycle-level
> first (the divider milestone's fragment), full regions after."*

with the emphasis:

> *"modelling the scheduler is very important to have full SV support."*

§8 re-cuts the ladder around this. The charter's own pricing note — *the
region ladder re-opens every theorem* — is the argument **for** doing it
early rather than against doing it at all: the cheapest moment for a
semantics change is before the theorem estate grows.

### 6.5 Editions — BOTH, with -2023 priority

> *"BOTH editions, 1800-2023 priority: adopt the family's
> sibling-editions layout — plan the move of the dormant tier's
> edition-sensitive files under Sv/V2023/ (census WHICH files are
> edition-sensitive first, the C tier's Value.lean lesson: measure,
> don't assume)."*

So the -2017/-2023 mixing this charter found (§2.1, §1.7) becomes a
concrete cleanup with a destination. **Census first**: which files are
actually edition-sensitive is to be *measured*, not assumed. The
starting evidence is in §7 — all 7 in-Lean edition tags are `-2017`,
concentrated in `Basic.lean`, while the corpus targets `-2023`.

### 6.6 The endgame — FULL SPEC SUPPORT

> *"ENDGAME = FULL SPEC SUPPORT, like every surface. The FP-divider
> (integer rung A then HardFloat) is a MILESTONE on the ladder, not the
> endgame — position it as the clause-4 cycle-level rung's flagship
> exit."*

§6's menu of three endgames collapses: options (a) and (b) were
milestones misfiled as destinations, and (c) — the completeness ladder —
is the endgame. **The scoreboard is coverage-by-clause against the
482-entry dictionary** the public suite already ships (§1.5).

---

## 7 THE DORMANCY RECORD — what 322 commits of law did while the lane slept

The lane stopped at `db9bb3e` on **2026-07-31** and this charter opened
at `39ea9ff` on **2026-08-22**: **322 commits, 22 days.** That window is
the C arc, and it is where most of this repository's *general* law was
written. The SV tier predates all of it.

**This section exists because a dormant tier does not merely fall
behind on features — it falls behind on RULES, and rules are invisible
until someone checks.** What follows is that check.

### 7.1 What the tier already satisfies BY ITS OWN ROUTE

The most useful finding is not the retrofit list — it is that the SV
lane independently invented a good deal of what later became law, and
in two places invented it *better*.

| law (later) | SV's independent route |
| --- | --- |
| **schedule-as-parameter + executable counterexample** (family §3.6) | `ScheduleOracle` bundles a choice function *with its legality proof*; `⊨` is `∀ σ stim tr`; `Sv.Deterministic` makes race-freedom a **per-design obligation, proved or refuted** (five designs prove it; `race_blk_not_deterministic` refutes it). `race_blk/spec.lean` runs one stimulus under `σ_src` and `σ_rev` as kernel-checked `#sv_check` pairs — the family document's illustrative example, **in the tree a month early** |
| four-constructor outcome covenant (§3.2) | `Sv.Res` reproduces the covenant's *semantics* (`.timeout` is fuel exhaustion and nothing else; `.unsupported` is loud and fuel-independent) with its own short-circuit simp lemmas |
| ∃-fuel + monotonicity (§3.2) | `Obs.lean` builds the ⊑-lattice, `run_mono`, and `Runs.at_least` as `∃ f₀, ∀ F ≥ f₀, …` |
| `--compare` staleness intent (§5.4) | `--recheck`: a fixed-seed determinism check against the stored census — half the law, invented independently |
| ingester REFUSES a provenance mismatch (§1.5) | `PDesign.crossCheck` refuses the envelope when the frontend's elaboration disagrees with the ingester's — the right mechanism, keyed on a different field |
| `maybe`-gated CI with reported SKIPs (§3) | both SV harnesses were `maybe`-gated from day one, a month before it became family law |
| goal-state-as-interface | 7 `#guard_msgs`-pinned delaborators |

**Two of these are stronger than the law that later replaced them**, and
§2.4 already records why: where C refuses what it cannot show
unobservable, SV proves over the whole schedule space.

### 7.2 What needs retrofitting — measured, and ranked

| # | gap | price | note |
| --- | --- | --- | --- |
| 1 | **`extractors/sv/census.py` is an instrument in the extractor tree** | one move | The family document names this as *the* one violation in the repository, to fix *"when the SV lane is next open."* It is open. `cv32e40p_census.py` is a second, unnoticed instance |
| 2 | **`--compare`, sorted output, committed artifact** | ~25 lines | **DONE with this charter's consolidation commit** |
| 3 | **`language_version` first-class in the envelope**, ingester refuses a mismatch | one function + 21 regens | SV is the family document's *named* failure mode: "one lane, two editions, no field that says so". Ruling 6.5 makes this load-bearing |
| 4 | **`frontend.version` must be the FAMILY, not a point release** | one line | **DONE for the census** (`pyslang-11`); the envelope still stamps `11.0.0` |
| 5 | **verdict vocabulary**: MATCH / REFUSE(cause) / DIVERGE / TIMEOUT | one function each | The harnesses speak PASS/FAIL only, and conflate timeout with unsupported. Ruling 6.3's oracle attribution lands in the same edit |
| 6 | **`docs_check` coverage is ZERO for SV docs** | one marker per block | 73/73 marked blocks pass repo-wide and **none is in an SV document**; the quickstart's 6 blocks are literally what a reader types |
| 7 | **one runner process per batch** | one function + lakefile line | `diff_test.py` spawns a fresh `lake env lean --run` per (case, σ). Affordable at 10 cases, fatal at corpus scale — and ruling 6.6 makes corpus scale the point |
| 8 | **`#print axioms` on the theorem set** | one block | 1 occurrence against 98 declarations |
| 9 | **the clause manifest** — generated and checked, never hand-maintained | one file, 30-60 rows | Highest long-run value: it is simultaneously the reader's view, the cross-edition gate, and ruling 6.6's scoreboard. **Uniquely cheap here** because `conf/lrm.conf` is a ready-made 482-entry dictionary |

**Deliberately not retrofitted.** `Sv.Res` → `Core/` unification is
structural, and the family document fixes its trigger on the C tier's
M2, not on SV. `LeanModels/Sv/SV2023/` waits on §6.5's census.

### 7.3 Two corrections this lane owes OUTWARD

1. **The family document's `Run σ α` count is wrong for SV.** It records
   *"Python (16 files) and SystemVerilog (3)"*. Re-derived:
   `grep -rn ': Run\b\|Run\.' LeanModels/Sv/*.lean` → **0**. The "3" is a
   bare-word match on doc comments ("Run one comb-phase process"). SV
   uses its own `Sv.Res`; **`Run σ α` has exactly one consumer, Python.**
   This matters because the move-to-`Core` trigger is fixed on the
   premise that SV is a second consumer.

2. **The theorem count, settled with its rule** (§7.4).

### 7.4 The counting rule, stated so the number stops drifting

Two lanes reported two numbers — 86 and 93 — which is how folklore
starts. The owning charter fixes the rule:

> **RULE.** A *proof-carrying declaration* is a `theorem`, `lemma` or
> `example` at the start of a line in `LeanModels/Sv/*.lean`, allowing
> optional `@[...]` attributes and `protected`/`private`/`nonrec`/
> `scoped` modifiers before the keyword.

Under that rule, measured today:

| | count |
| --- | ---: |
| `theorem` | 93 |
| `example` | 5 |
| `lemma` | 0 |
| **TOTAL** | **98** |

**Reconciliation in one line:** the sibling lane's **93** is this count
restricted to `theorem`; this charter's earlier **86** was a regex that
required the keyword at the start of the line and so silently dropped
the 12 attribute- and modifier-prefixed declarations. **98 is the
number**; 93 is reproducible as "theorems only".

---

## 8 THE LADDER — re-cut for full-spec support

The endgame is **full spec support** (§6.6). The scoreboard is
**coverage-by-clause against the 482-entry dictionary**. What follows is
the rung order, and the one sequencing question the rulings left open.

### 8.1 THE SEQUENCING DECISION: the scheduler goes EARLY, and here is the number

Ruling 6.4 puts the full scheduler in scope; the emphasis puts it early.
The charter priced the upgrade as *"re-opens every existing theorem"*,
so the decisive metric is **how much estate a trace-type change
re-opens, and how fast that estate is growing.**

Measured today — **and re-measured in `docs/sv-r1-scheduler.md` §0,
which corrects this table**. The figures first published here were
scoped wrong twice: they counted only `LeanModels/Sv/` and their regex
missed the `⊨`/`⊑` surface forms, so they excluded every theorem about
an actual design. The corrected estate:

| estate | proof-carrying | trace-shaped |
| --- | ---: | ---: |
| `LeanModels/Sv/` | 98 | 61 |
| `Examples/system-verilog/` | 133 | 95 |
| **TOTAL** | **231** | **156 (68%)** |

*(As first published: "50 of 98, 51%".)*

**Two thirds of the estate is trace-shaped, and it is the part that
grows with every rung.** The correction does not weaken the ordering
below — it strengthens it, and R1's design then makes the number nearly
moot by routing all 156 through a single adequacy lemma
(`docs/sv-r1-scheduler.md` §5). Under the region upgrade the trace type changes from *one
snapshot per cycle* to *one per time slot with region structure*, so
those 50 re-open. Every construct rung completed first adds to that 50.

**Decision, and it follows the emphasis:** *the full scheduler is the
rung immediately after consolidation.* Doing breadth first would buy
clause coverage at the cost of compounding the one refactor that touches
half of everything — and under the doctrine the scheduler **is** the
tier's definition, because the `∀ stim σ tr` quantifier that every
theorem is stated under ranges over clause 4. A tier whose central
quantifier ranges over a placeholder is not a tier that has defined
correctness completely.

### 8.2 The divider exemplar — both orders priced, and the choice

Ruling 6.6 makes the FP divider *"the clause-4 cycle-level rung's
flagship exit"*, which sits in tension with 8.1's ordering. Priced both
ways:

**Order A — divider first, stated scheduler-parametrically.** The
good news: **∀-over-σ is already free.** Every SV theorem is stated as
`∀ stim σ tr, Runs d σ stim tr → P`, so schedule-parametricity is not
something to add — it is the tier's existing shape. What is *not* free
is **trace-type stability**: the divider's observable is a cycle-indexed
projection, and after the upgrade "cycle" is a derived notion.
Parametricity therefore costs one abstraction function
`cycleOf : Trace → CycleTrace` plus an **adequacy lemma** saying the
region semantics projects onto the cycle semantics for designs in the
cycle-level fragment. Price: the adequacy lemma is the real work — it is
the theorem that the two models agree, and it cannot be cheap because it
is exactly the content of the upgrade. Divider theorems then survive
untouched.

**Order B — scheduler first, divider after.** Zero divider theorems
re-open, because none exist yet. The adequacy lemma is still wanted (see
8.3) but is no longer on the divider's critical path.

**Chosen: Order B, with one exception.** The adequacy lemma has to be
written either way, and writing it *before* there is a divider estate to
protect means writing it once against 50 declarations rather than twice
against 50-plus-N. The exception is **rung A, the integer divider**: its
SV side is already ingested and in-tier, so if a demonstrable theorem is
wanted before the scheduler lands, `cv32e40p_alu_div` is the cheap one
to state — and it should be stated *through* `cycleOf` from the first
line, so it is Order-A-shaped and survives.

### 8.3 The rungs

**R0 — CONSOLIDATION. (Largely landed.)** The four instrument defects
closed, the round-trip gate green at 18/18, the census committable and
`--compare`-checkable. Remaining: retrofits 1, 5, 6, 7 of §7.2, and
`language_version` (retrofit 3) which ruling 6.5 makes load-bearing.

**R1 — THE SCHEDULER. Clause 4 in full.** **Designed in
[docs/sv-r1-scheduler.md](sv-r1-scheduler.md)** — the region census, the
determinism boundary, the Lean shape, the `cycleOf` adequacy lemma, the
divider's statement shape, and nine priced inches. Census-first, per the
ruling:

1. **Census the region semantics before modelling it** — the nine
   regions (Preponed, Active, Inactive, NBA, Observed, Reactive,
   Re-Inactive, Re-NBA, Postponed) plus the PLI regions, which are in
   scope under 6.3. Enumerate, for each: what enters it, what may
   reorder within it, and what the standard *fixes*.
2. **Draw the determinism boundary explicitly** — what within a region
   is ∀-quantified versus ordered. This is the `ScheduleOracle`'s new
   contract and the single most important artifact of the rung.
3. **Map the existing cycle model onto it.** The upgrade must be an
   **extension** where the cycle model is a faithful projection, and a
   **supersession-with-adequacy** where it is not — and *never a silent
   replacement*. The definition-change discipline applies to our own
   tiers: if `cycleStep` stops meaning what it meant, that is a recorded
   change with an adequacy lemma, not a quiet edit.
4. Then the semantics, then re-establish the 50 trace-shaped
   declarations through the projection.

Unlocks `initial`, `#` delays, clocking blocks (cl. 14), program blocks
(cl. 24) — and therefore most of the verification tier's *timing*.

**R1-exit — THE DIVIDER FLAGSHIP.** Integer first
(`cv32e40p_alu_div`, already ingested), then IEEE 754 via Berkeley
HardFloat's `divSqrtRecFN` (§6.2's obstacles stand: the `recFN`
recoding, and it is Verilog not SV). Gated on the shared SoftFloat spec
layer, which is not SV work.

**R2..Rn — BREADTH BY CLAUSE**, ordered by the census's own priority
queue rather than by taste. Today's blockers on the public suite are
**signedness and range metadata** (`VariableSymbol:signed`,
`NamedValueExpression:signed`, `VariableSymbol:range`) — unglamorous,
and the highest-frequency thing in the way. The verification tier
(cl. 8, 18, 19) enters here, after R1 has given it a clock to hang on.

**Scoreboard, every rung:** clauses covered / 482, generated and
checked, never hand-maintained.

---

## 9 WHAT REMAINS OWED

The six decisions are taken. What is still outstanding is not a decision
but an **access** and two standing obligations.

1. **Xcelium access — machine and licence.** Ruling 6.3 makes Xcelium
   the oracle where Icarus falls short. The details are owed by Thomas.
   **The design must not block on it**: the oracle is a parameter,
   Icarus is the default, and per-test oracle attribution is recorded
   from the first commit that touches the harness.

2. **The Xcelium 4-state table is UNVERIFIED on any reachable host.**
   `docs/sv-design-m0.md` calls its operator table *"normative —
   verified on Xcelium"*. Icarus reproduces the 10 harness cases today,
   but the **operator-level table has not been re-checked here**. No new
   claim may call it dual-simulator-verified without a re-run — and
   ruling 6.3 supplies the mechanism to do so properly.

3. **`sv-tests-2` stays out of public artifacts** until the
   open-sourcing ruling, and **the IEEE PDF stays unopened**. Both are
   standing conditions of ruling 6.1, not one-time checks.

---

## 10 WHAT LANDED WITH THIS CHARTER

The charter itself, backlog §L60, and — in the consolidation commit that
followed it — `harness/sv_round_trip.py`, a rebuilt
`extractors/sv/census.py`, and `docs/sv-construct-census.json`.

**Every headline is a run**: the harness 10/10 green vs Icarus 12.0; the
round-trip **18/18 byte-identical, 3 documented SKIPs**; the build
3 690/3 693 jobs with zero compilation errors and all 14
`LeanModels.Sv.*` built (two Python-tier targets SIGTERMed under
contention — a resource kill, not a proof failure); **98** proof-carrying
declarations under §7.4's rule, 0 `sorry`, 0 `native_decide`; the
frontend gap and its one-minute fix; the gitignored census; the dead
corpus path; the corpus disjointness; the licence censuses; the pyslang
SIGTRAP and the `Pool` hang it caused; and the full 717-file public
census now completing in **1.0 s** where it previously never completed
at any job count.

**THREE corrections the charter made to itself**, all kept visible
because instrument faults are findings:

1. The first round-trip run reported 12 failures that were the
   *charter's* invocation error — **read the mode out of the artefact.**
2. §1.6 began by asserting that switching the anchor corpus was *"a
   licensing decision, not an engineering one"*; running the instrument
   refuted it.
3. **The 18th envelope was never broken.** The charter published
   *"17 of 18, 1 absent input"* and blamed a missing `cv32e40p_pkg.sv`.
   Wrong on both count and cause: the file
   `cv32e40p_register_file_ff.sv` declares module
   `cv32e40p_register_file`, so a `--top` derived from the *filename*
   could not resolve it. Read from the envelope, it regenerates
   byte-identically with no external checkout. **18 of 18.** The
   plausible-but-unverified diagnosis survived one whole publication,
   which is the argument for the gate that now runs it.

**Not one of the three was visible without executing the thing.** That
is the entire case for census-first, and this lane has now paid for it
three times.
