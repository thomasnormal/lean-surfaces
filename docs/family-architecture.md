# The FAMILY architecture: versioned language surfaces

**Status: the family's founding charter.** Thomas chartered the repository
as a FAMILY of VERSIONED language surfaces on 2026-08-22: spec-mirrored
where a spec exists (C per edition, SystemVerilog per edition, and three
tiers founding now — WebAssembly, ECMAScript, Ada), reference-interpreter-
extracted where none does (Python per CPython minor). A user chooses the
proof target by naming a language and a version.

This document exists so that the lanes lay down the same structure — three
of them **founding** a tier from nothing (WebAssembly, ECMAScript, Ada) and
three **consolidating** one that already exists and works (SystemVerilog,
RISC-V, Verilog-A). §1.2 records which is which, because mistaking the
second for the first prices a rebuild of working code. It **constrains**;
the lanes implement. It carries **no Lean restructuring** of its own: every
ruling below is a rule the lane that next touches the code obeys.

**Everything decision-relevant here was measured.** Two instruments landed
with this charter (§10) and their outputs are cited inline; nothing is
quoted from memory, and §2's central question — copies, deltas, or
parameters — is decided by numbers rather than by taste.

**Three recorded beliefs were corrected by measurement**, which is the
best argument for the instruments existing at all:

* the C tier's own ISO citations are three-of-five an edition out of date
  (§2.5) — found by the clause instrument, in the lane founding the
  versioned layout;
* `Std.Do`'s triple/WP stack and the `mvcgen` tactic are **already present
  on the pinned toolchain** (§3.4), so the "a bump would touch every lane"
  caveat is retired rather than carried;
* **Lean's `Float` is kernel-reducible on the pinned toolchain** (§3.5),
  which is the premise three tier documents defer floats on. Core ships
  1856 lines of width-parametric IEEE 754 model, and it reduces.

---

## 0 THE DOCTRINE, and what is being unified

### 0.1 Three principles, and they govern every tier

Thomas, on what this family is for:

> *We are not saying it'll be easy to prove correctness of arbitrary
> threaded C programs. It might be really really hard or undecidable. But
> we want to make it possible to DEFINE correctness, and it's the burden of
> the prover to find a proof. We can give some tools, tactics and so on,
> but ultimately if it's too hard to prove, the program should probably be
> rewritten.*

Everything below follows from that, and the three principles are the form
it takes in this repository.

**I. THE DEFINITION IS NEVER WEAKENED FOR PROVABILITY.** The semantics'
one job is a **sound and complete definition of correctness** — ∀ schedule,
∀ evaluation order, ∀ resolution of every nondeterminism the language
admits. **Definitional completeness outranks proof convenience, always.**
If the honest definition quantifies over a space no tactic can search, the
definition still quantifies over it. Undecidability of the general problem
is **accepted at the definition layer** and is not an argument against the
definition; a semantics that narrowed its ∀ to what the current library can
discharge would be measuring the library and calling it the language. This
is the same law the tiers already obey when they REFUSE rather than invent
a rule (§4.2), stated at the level that governs all of them.

**II. THE TRUST BOUNDARY, and it is drawn tightly.** Two strata, and only
one of them is trusted:

| stratum | contents | property |
| --- | --- | --- |
| **the DEFINITION** — trusted, kept **minimal** | the interpreter, the spec citations, the verdict system | soundness and completeness are its obligations; every addition is a liability and is argued for |
| **the LIBRARY** — trusted **never**, growable **forever** | tactics, mover/commutativity lemmas, `Spec`/`@[spec]` collections, `mvcgen` integrations, altitude lemmas | **incomplete by design.** Its incompleteness is expected, published, and never hidden |

A library lemma cannot make a wrong program right, because nothing in the
library is believed — it only ever produces a proof the kernel rechecks
against the definition. That asymmetry is what lets the library grow
without bound and without review anxiety, and it is why the library's gaps
are reported as gaps rather than papered over. **This is exactly why §3.6's
proof-burden tiers — bounded-fixture exhaustion, mover lemmas, ownership
reasoning — are a LIBRARY section and not part of the semantics.** They are
three ways to find a proof of a statement whose meaning was already fixed
without reference to them.

**III. HARDNESS IS A SIGNAL TO THE PROGRAM, not to the definition.** When a
proof will not come, the framework owes the user a next step, and there are
exactly two — both constructive, neither touching the definition:

* **(a) A counterexample is found.** Search turns up a breaking schedule,
  order or resolution, and it lands as a **kernel-checked witness** —
  §3.6's counterexample-as-artifact, a finite concrete schedule replayed by
  `#guard`. The verdict is not "unproven"; it is **the program is wrong**,
  here is the run. Fix the program.
* **(b) No witness is found AND the proof resists the library.** Then the
  program's correctness is, in the precise sense this repository can
  measure, **unarguable** — and that is information about the program.
  **Rewrite toward provability.** The discipline that says "use mutexes and
  `memory_order_seq_cst`, not hand-rolled relaxed atomics", or "structure
  your concurrency", has always been cultural advice backed by folklore.
  **This framework turns it into a formal pressure**: the DRF-SC fence
  (§3.6, piece 3) is the standard's own clause, so a program that stays
  inside it is one the tooling can actually reason about, and a program
  that leaves it has left on purpose and pays for it.

Neither exit ever weakens the definition, and a third exit — narrowing the
∀ until the theorem goes through — is **not available**. That is the whole
doctrine: the definition is the contract, the library is the help, and the
program is the variable.

### 0.2 What is being unified, and what is not

Seven language lanes exist today. Measured (`.lean` lines under
`LeanModels/`):

| lane | lines | authority | outcome type | source spans |
| --- | ---: | --- | --- | --- |
| Python | 32331 | CPython 3.9 (extraction) | `Run σ α` | `LeanModels.Span` |
| Spice | 23366 | ngspice (extraction) | none — contracts | `Circuit.Spice.SourceSpan` |
| SystemVerilog | 8166 | IEEE 1800 (spec) + pyslang | `Sv.Res α` | none |
| Circuit | 4309 | physical law | none — enclosures | `Circuit.Spice.SourceSpan` |
| RISC-V | 2041 | RISC-V ISA (spec) | none — step relation | none |
| C | 934 | ISO/IEC 9899 (spec) + clang | `CRes α` (value layer) | `LeanModels.Span` |
| Verilog-A | 606 | OpenVAF (extraction) | none | `VerilogA.Span` |
| **Core** | **13** | — | — | — |

**`LeanModels/Core/` is 13 lines of 71 766 — 0.018% of the model tree.**
It contains one structure. That number is the honest starting point for
every claim about a "shared substrate" and it is why §3 is written the way
it is: the substrate is today an *aspiration with one instance*, and this
document's job is to make it a gated boundary instead of an accident.

**What is NOT unified, deliberately:** the Circuit and Spice lanes — the
second-largest body of Lean in the tree — do not use `Run` and are not
asked to. They model continuous state by enclosure and contract, which is
a different architecture and a correct one for their subject (§7.3).

---

## 1 THE LAYOUT CONVENTION

### 1.1 The rule

    LeanModels/<Lang>/                 -- version-NEUTRAL: what every claimed edition shares
    LeanModels/<Lang>/<Ver>/           -- version-SCOPED: what an edition decides for itself

`<Lang>` is the language's directory tag; `<Ver>` is its **edition token**.
Both come from the registry (§1.2), which is a table and not a derivation
rule, because a mangling clever enough for C and Python breaks on the
fourth language.

An edition token obeys four laws:

1. **It is a valid Lean identifier** beginning with a letter. This is not
   style: `LeanModels/Python/3.12/` is not a module name.
2. **It is self-identifying out of context.** `LeanModels/C/V23/Value.lean`
   in a stack trace tells a reader nothing; `LeanModels/C/C23/Value.lean`
   tells them everything. The stutter in `LeanModels.C.C23` is accepted as
   the price of that, and it is a good price.
3. **It names an edition a reader can hold** — a published document, or a
   released interpreter's minor line. Never a point release, a patch
   level, or a build. The C envelope already applies this rule to the
   compiler (`apple-clang-17`, the FAMILY); the Python envelope does not
   (§1.5), and the correction is overdue.
4. **It never renames.** The token appears in every envelope, every module
   path and every citation, so a rename is a tree-wide re-extraction. The
   backlog prices that event twice; do not create a third.

### 1.2 The registry

Rows marked **PROPOSED** are the founding lane's to measure and ratify;
the lane's first landed artifact is its census, and the census is what
turns the row from proposed into recorded (§8).

**`state` distinguishes the two jobs a lane can have**, and getting it
wrong mis-prices the work: *founding* builds a tier from nothing;
*consolidation* takes an existing body of Lean and gives it the family's
structure. Three of the rows below are consolidation and were nearly
mislabelled.

| language | `<Lang>` | authority | edition tokens | oracle | corpus | state |
| --- | --- | --- | --- | --- | --- | --- |
| C | `C` | spec-mirror — ISO/IEC 9899 | `C23` (now), `C17` (if claimed) | clang, pinned family + profile | `ctwin/sunfish.c`; c-testsuite; gcc torture | active — M2 |
| Python | `Python` | extraction — CPython | `Py39` (now) | CPython 3.9, pinned family | `Examples/python/**`; the stdlib sweep | active — mid-campaign |
| SystemVerilog | `Sv` | spec-mirror — IEEE 1800 | `SV2017`, `SV2023` — **PROPOSED** | pyslang frontend; a simulator | **public `sv-tests`** (see below) | **CONSOLIDATION** — 8 166 lines, dormant but verified working |
| WebAssembly | `Wasm` | spec-mirror — W3C core | **PROPOSED** | the reference interpreter | the official `.wast` suite | founding |
| ECMAScript | `Es` | spec-mirror — ECMA-262 | **PROPOSED** | an engine | test262 | founding — blocked on SoftFloat (§3.5.3) |
| Ada | `Ada` | spec-mirror — ISO/IEC 8652 | **PROPOSED** | a compiler | ACATS | founding |
| RISC-V | `Rv` | spec-mirror — RISC-V ISA | **PROPOSED** | the ISA oracle | `harness/rv` | consolidation — 2 041 lines |
| Verilog-A | `VerilogA` | extraction — OpenVAF | — | OpenVAF | `Examples/verilog-a` | consolidation — 606 lines |
| SPICE | `Spice`/`Circuit` | extraction — ngspice | — | ngspice | `Examples/spice` | active — 27 675 lines, separate architecture (§6.1) |

The last three carry no edition token today. That is allowed and it is
what §1.4 rules on: **a language earns version directories when its tier
claims an edition, not before.**

**The SV row was corrected twice, and both corrections generalize.**

*The corpus.* This document first named **sv-tests-2** as the SV corpus,
copying `docs/sv-corpus-coverage.md`. It cannot stand: that corpus sits in
a clone with **no license**, 21 631 files, and an **embedded IEEE 1800-2023
PDF** — 9.4 MB of vendored IEEE text, against this repository's own
no-vendoring law (§2.1, §10) — and its provenance names a private
organization, which the no-private-hostnames rule covers. The clean anchor
is the **public `sv-tests`**: uniform ISC, per-file SPDX, `tests/**` only
(`generated/` reaches GPL ivtest), and **already clause-mirrored** — 326
clause tags against a 482-clause LRM dictionary, which is a coverage-by-
clause manifest (§5.5) that already exists and did not have to be built.
**Whether sv-tests-2 may be used at all is an open Thomas decision** and
nothing should depend on it meanwhile.

Two family rules fall out. **A corpus's LICENSE and PROVENANCE are part of
its registry row, not a detail discovered later** — the C tier learned this
when reading 219 `.otag` files split c-testsuite into ISC and LGPL halves,
and the founding checklist (§8) now carries it at step 0. And **a corpus
that vendors the standard it tests against is disqualified by our own
law**, however convenient it is.

*The maturity.* The SV tier is **not greenfield**: `LeanModels/Sv/` is
**8 166 lines** (measured) with a differential harness recorded green
against Icarus, dormant rather than absent. Labelling it "founding" would
have priced a rebuild of work that exists and passes. Its theorem count is
the SV charter's to state — this document's counting rule gives 93
`theorem`/`lemma` declarations in the lane where that charter says 86, and
two counting rules disagreeing is exactly the kind of number a charter
should own rather than a neighbour quote.

**One standing violation, flagged and not fixed here.**
`docs/sv-corpus-coverage.md` line 5 records a corpus path under a private
home directory and organization. That breaches the same rule this
correction invokes. It is the SV lane's file and their charter is in
flight, so it is theirs to redact — but it is named here so it is not lost.

### 1.3 The version-neutral boundary, stated per language

The neutral layer is the **measured INTERSECTION** of the editions the
tier claims. It is not "the oldest edition" and it is not "the part that
felt general". It is a claim with an instrument behind it, and when the
claim stops holding the construct moves down.

**C — measured.** `LeanModels/C/{Ast,Json,Load}.lean` are version-neutral,
and the evidence is `docs/c-construct-census.json`: **zero of the 45 AST
node kinds the tier ingests is post-C99.** The censused vocabulary is
`BinaryOperator`, `CompoundStmt`, `DeclStmt`, `ForStmt`, … — the C89/C99
core, with no `_BitInt`, no `GenericSelectionExpr`, no `StaticAssertDecl`,
no attribute node. A C17 surface would ingest the same 45 kinds through
the same ingester.

`LeanModels/C/Value.lean` is version-SCOPED, and the evidence is **one or
two lines, and the line is `IntTy.minVal`.**

C23 §6.2.6.2p2 fixes the sign bit's value: *if the sign bit is one, it has
value −(2^(N−1))* — a single stated value, which is two's complement. C17
§6.2.6.2p2 instead offers **three** representations — sign-and-magnitude,
two's complement, ones' complement — and says *"which of these applies is
implementation-defined."* So `INT_MIN` is `-(2^31)` in C23 and one of two
values in C17, and **`minVal` is the definition that differs.** The
confirming change-history note is §6.2.6.2p6 NOTE 2, which names the
representation and records that prior editions allowed others; the
**normative** mandate is p2, and the distinction matters here for the same
reason it matters in §3.6 — a NOTE is informative, and a tier that cited
one as normative would be overclaiming.

The auditable trace is in Annex J: **C17's implementation-defined integers
list has FIVE entries and C23's has FOUR**, and the deleted one is exactly
*"whether signed integer types are represented using sign and magnitude,
two's complement, or ones' complement …"* (C17 J.3.5; C23's list is J.3.6,
itself renumbered and item-numbered per §2.1).

**CORRECTION — this section previously cited `convert` and §6.3.1.3, and
that was wrong.** §6.3.1.3p3 is **word-for-word identical** in C17 and
C23 — *"either the result is implementation-defined or an
implementation-defined signal is raised"* — and **C23 J.3.6 item (3) still
lists it** as implementation-defined. Out-of-range unsigned→signed
conversion is therefore **not** C23-mandated; it is profile-pinned
(`uint_to_int_wraps`) in every edition, which is where `docs/c-profile.md`
already had it. The error was inherited from the tree's own prose and then
appeared to be confirmed by this charter's instrument, which reported
clause 6.3.1.3 as *changed* at ratio 0.989 — but that change is `_Bool` →
`bool` in p1 and a footnote renumbering, not p3. **A similarity ratio says
a clause MOVED; it never says WHAT moved.** That is the precise failure
mode §5.5's clause manifest exists to prevent, and it caught the author of
§5.5. Found and corrected by the C M2 lane; verified here against both
drafts before being propagated.

**The conclusion survives the evidence swap**, which is why it is worth
stating twice: 933 of 934 lines are common to both editions, and the
version-scoped part of the C value tier is one definition — just a
different one.

**Python — measured.** The AST tier, the ingester, the interpreter and the
whole proof layer are neutral across 3.9→3.14 on everything the corpus
reaches (§2.3): 1458 rows, **100.00% value-identical**. What is version-
scoped is the **error-message surface**, and it is scoped more deeply than
a string table: `PyErr` encodes zero-division as *two* nullary
constructors because CPython 3.9 has exactly two texts; 3.11 and 3.12
split it *three* ways. A 3.11 surface needs a different constructor
ARITY. So `PyErr` and `errMessage` are version-scoped; `Semantics.lean`,
`Runtime.lean` and the VC layer are neutral.

**Every other lane: state the boundary before writing the second
edition's first line.** The boundary is cheap to draw while the scoped
part is small and expensive afterwards, which is the same argument that
put C's effective types in at zero sites.

### 1.4 The C lane's `LeanModels/C/C23/` — RATIFIED, with one refinement

The C lane is adopting `LeanModels/C/C23/`. **Ratified**, for three
reasons, and refined in one.

*Ratified because the naming IS the claim.* A tier that models C23 and
says only `LeanModels/C/` claims all of C. §2.1 measures that C23 and C17
share 21.4% of their substantive clause text; a directory that declines to
say which one it means is making a claim it cannot support.

*Ratified because the level is free now and costly later.* Adding it after
M2 is a rename of every module in the lane, and law 4 above exists because
the backlog prices that event twice.

*Ratified because `C23/` fills up fast.* It holds one file today. M2's
inches 2–5 — memory model, expression semantics, statements, calls — are
all rules an edition decides, so within the priced ~15–20 sessions
`C23/` holds most of the tier.

**REFINEMENT: only the version-scoped files move.** `Ast.lean`,
`Json.lean` and `Load.lean` stay at `LeanModels/C/`, because the census
measured their vocabulary neutral (§1.3) and moving them would assert an
edition-dependence that does not exist. `Value.lean` moves to
`LeanModels/C/C23/`. The C lane implements; this document does not.

**IMPLEMENTED, and independently confirmed.** The C M2 lane has taken this
layout, and in doing so verified §2.1's renumbering result and this
section's split from their own reading of the drafts rather than from this
document. Two lanes reaching the same clause facts by different routes is
the only kind of confirmation worth having — and the same exchange
corrected §1.3's evidence, which is the other kind.

### 1.5 `language_version` becomes a first-class envelope field

**Measured defect: no envelope in the family carries the language version
as a field.** Read off the tree:

| lane | where the language version lives today | verdict |
| --- | --- | --- |
| Python | `frontend.version: "3.9.19"` | the INTERPRETER's point release, conflated with the language edition |
| C | `profile_flags[0] == "-std=c23"` | a substring of a flag list; an ingester must string-parse to ask "which C?" |
| SystemVerilog | nowhere | the lane cites IEEE 1800-**2017** for operator semantics (`docs/sv-design-m0.md`) and censuses the IEEE 1800-**2023** conformance corpus (`docs/sv-corpus-coverage.md`) |

The SV row is the failure mode in the wild: one lane, two editions, no
field that says so, and nothing that could have noticed.

**Ruling.** Every envelope gains

    "language_version": "<the registry's edition token>"

as a first-class top-level field, next to `language`. Its value is the
same string that names the directory, so path, envelope and citation
cannot drift. The ingester REFUSES a mismatch, exactly as
`load_c_program` already refuses a `profile_id` mismatch — an envelope
from another edition is a different program.

`frontend.version` keeps its own job and its own correction: it is the
FRONTEND's family (`apple-clang-17`, `cpython-3.9`), never a point
release. That rule is recorded twice in `docs/backlog.md` and cost 53
files of re-extraction the second time; the Python envelope still carries
`3.9.19` and should carry the family.

Schema versions (`0.1`, `sv-0.1`, `c-0.1`) are unaffected. They version
the ENVELOPE FORMAT and are orthogonal to the language edition; conflating
the two is the mistake this field prevents.

### 1.6 The other four surfaces

The convention is not only about `LeanModels/`. Four more directories
carry the family pattern, and the rules differ because their subjects do.

* **`extractors/<lang>/extract.py` — ONE extractor per language, never per
  edition.** The frontend is a single tool that takes an edition switch:
  clang takes `-std=`, CPython is the binary you invoke. `extractors/c/
  extract.py` already hard-codes `PROFILE_FLAGS = ["-std=c23", …]`; that
  constant becomes a parameter, and the extractor stamps the resulting
  `language_version` into the envelope.
* **`Examples/<lang>/<name>/` — the corpus is NOT versioned by path.** The
  same `.c` extracts under two editions; the envelope's
  `language_version` says which one this artifact is. A second edition's
  envelope of the same source sits beside the first under a name that
  carries the token.
* **`docs/<lang>-*.md` — keep the existing convention** (`c-*`, `sv-*`,
  `spice-*`, `rv-*`). Add `<lang>-<ver>-*.md` only for a document that is
  genuinely edition-specific; a census of a corpus is, a design of a
  memory model usually is not.
* **`harness/<lang>_<subject>_census.py` — instruments live in
  `harness/`.** One exception exists and is a defect to fix when the SV
  lane is next open: `extractors/sv/census.py` is an instrument living in
  the extractor tree. Extractors extract; instruments measure.

---

## 2 COPIES, DELTAS, OR PARAMETERS — decided by measurement

Two censuses landed with this charter, one per authority style. They
disagree about the *documents* and agree about the *models*, and that
disagreement is the whole architecture.

### 2.1 The C17 → C23 clause census

`clause_delta.py`, run on the two public working drafts (N2310 for C17,
N3220 for C23). **No ISO text is reproduced anywhere in this repository**
— the instrument emits clause numbers, clause TITLES and similarity
ratios, and nothing else.

*Method, because the first answer it gave was wrong.* Matching clauses by
NUMBER measures the renumbering, not the change: C23 shifted 6.5.4 onward
by one, so C17's `6.5.7 Bitwise shift operators` is C23's `6.5.8`, and
C17's `5.1.2.3 Program execution` is C23's `5.1.2.4 Program semantics`.
Both were verified by direct grep of the drafts, independently of the
parser. The instrument therefore matches on the **ancestor-title path**,
with a rescue pass by (top-level number, own title) for clauses whose
PARENT was retitled. Two PDF renderings never produce byte-identical text,
so identity is reported at a ratio threshold of 0.995 with exact equality
reported separately as a floor; clauses whose body is a heading over
subclauses are flagged `thin` and excluded from ratio statistics. The
instrument refuses loudly on a missing input, a zero-clause parse, or an
implausible count, and its output is byte-identical on a re-run.

**Headline.**

| quantity | value |
| --- | ---: |
| body clauses located — C17 (N2310) | 996 |
| body clauses located — C23 (N3220) | 1267 |
| matched across the two editions | 933 |
| …of which substantive (excluding heading-only `thin` rows) | 679 |
| **identical, ratio ≥ 0.995** | **145 of 679 — 21.4%** |
| changed | 534 |
| added in C23 | 334 |
| removed | 63 |
| **renumbered — same clause, different number** | **612 of 933 — 65.6%** |

Similarity buckets over all matched rows: ≥0.995 — 282; 0.95–0.995 — 145;
0.80–0.95 — 148; <0.80 — 358. Normalizing away cross-references and
footnote numbers, which the renumbering moved wholesale, shifts identity
only from 27.9% to 31.0% of matched rows: **the churn is real edits, not
citation drift.**

**By subtree — the language clauses the C tier models.**

| subtree | total | identical | changed | added | removed |
| --- | ---: | ---: | ---: | ---: | ---: |
| 5.1.2.3 program execution (sequencing) | 6 | 2 | 2 | 1 | 1 |
| 6.2.1–6.2.4 scope / linkage / storage duration | 6 | 0 | 2 | 2 | 2 |
| 6.2.5 types | 1 | 0 | 1 | 0 | 0 |
| 6.3 conversions | 15 | 4 | 10 | 1 | 0 |
| 6.5 expressions and operators | 34 | 3 | 26 | 4 | 1 |
| 6.6 constant expressions | 1 | 0 | 1 | 0 | 0 |
| 6.7 declarations | 38 | 0 | 19 | 18 | 1 |
| 6.8 statements | 20 | 3 | 13 | 4 | 0 |
| 6.10 preprocessing directives | 26 | 1 | 16 | 8 | 1 |
| J.3 implementation-defined behavior | 16 | 0 | 13 | 2 | 1 |

**Spot-checked, five clauses, before the table was believed.** 6.3.1.3
*Signed and unsigned integers* — ratio **0.989**, a small targeted edit.
**A spot-check that was itself over-read**, and the lesson is recorded in
§1.3: the 0.989 is `_Bool` → `bool` in p1 plus a footnote renumbering, and
this document originally read it as C23's two's-complement mandate. It is
not — p3 is word-for-word identical across the editions. **A ratio locates
a change; only reading the clause identifies it.** 6.2.5
*Types* — **0.245**, large, as predicted. C17 6.5.3 → C23 6.5.4 *Unary
operators* — **0.986**, the near-unchanged control. C17 6.5.7 → C23 6.5.8
*Bitwise shift operators* — **0.310**. `7.13.2.1 The longjmp function` —
**0.776**, matched by the title rescue because its parent was retitled;
without the rescue pass the instrument reported it REMOVED, which is the
defect the rescue pass exists to fix and it was found by spot-checking.

**Annex J.2 — the refusal taxonomy's own delta.** The enumerated
undefined-behavior list runs **211 items in C17 and 221 in C23**. Matched
modulo the trailing clause citation (which the renumbering moved): **171
identical, 40 only in C17, 50 only in C23.** So 77% of C23's UB list is
carried over, and a fifth of it is new. One presentational change is
load-bearing for a tier whose refusal causes are J.2-shaped: **C23
NUMBERED the items** — `(1)`, `(2)`, … — where C17's are unnumbered
bullets. A C23 refusal can cite a UB item by number; a C17 refusal cannot.

### 2.2 The C model's own delta — and it is one line

Against 21.4% clause-level identity, the tier that mirrors those clauses
measures:

* **0 of 45** ingested AST node kinds are edition-specific (§1.3).
* **1 of 11** value-layer definitions is edition-sensitive — `IntTy.minVal`,
  because C23 §6.2.6.2p2 fixes the sign bit's value where C17 §6.2.6.2p2
  left the choice among three representations implementation-defined
  (§1.3, which also records the wrong answer this bullet used to give).
* **933 of 934** lines of `LeanModels/C/` are common to C17 and C23.

**These two measurements are not in conflict and confusing them is the
error this section exists to prevent.** The standard changed enormously;
the modeled fragment did not. C23's edits landed in declarations (6.7: 18
new subclauses, 0 identical), preprocessing (6.10: 8 new, 1 identical) and
the library — and the tier models a 45-kind C89-era vocabulary that C23
left almost alone. **The delta that prices the architecture is the delta
over the CLAIMED CLAUSES, never the delta over the document**, and it can
only be known by an instrument that knows which clauses are claimed. That
instrument is the clause manifest (§5.5), and this measurement is the
reason it is not optional.

### 2.3 The CPython 3.9 → 3.12 census

Two instruments, on the two surfaces the repo already gates.

**Behavior — the differential corpus, run under four interpreters.** 1458
rows (1394 expanded `cases.json` calls plus the 65 whole-program scripts)
executed under CPython 3.9.19 / 3.11.11 / 3.12.8 / 3.14.5, deterministic
across two full runs (identical output sha256), one ERROR row reported and
not dropped (a corpus function that returns the real wall clock, and is
therefore nondeterministic under every interpreter).

| | measurable | value-identical | message-identical |
| --- | ---: | ---: | ---: |
| 3.9 → 3.12 | 1458 | **1458 — 100.00%** | 1427 — 97.87% |
| 3.9 → 3.14 | 1458 | **1458 — 100.00%** | 1399 — 95.95% |

**Not one value semantic changed.** Zero rows changed a returned value, an
exception class, a stdout byte or an exit code at any step. All 59 deltas
are exception MESSAGE TEXT, in eight named buckets — zero-division
rewordings 17, builtin-message rewordings 10, qualified callable names 9,
unbound-variable rewordings 9, unhashable rewordings 8, attribute-error
suffixes 3, recursion-limit messages 2, and one "Did you mean:" suffix.

**Grammar — the `ast` module, per version.** The instrument re-derives
`docs/completeness.md` §2's counts on 3.9 exactly (25 statements, 27
expressions, 13 binary, 4 unary, 10 comparison, 2 boolean operators),
which is its validation.

| sort | 3.9 | 3.11 | 3.12 | 3.14 |
| --- | ---: | ---: | ---: | ---: |
| `stmt` | 25 | 27 | 28 | 28 |
| `expr` | 27 | 27 | 27 | 29 |
| `operator` / `unaryop` / `cmpop` / `boolop` | 13/4/10/2 | 13/4/10/2 | 13/4/10/2 | 13/4/10/2 |
| `pattern` | 0 | 8 | 8 | 8 |
| `type_param` | 0 | 0 | 3 | 3 |

Cumulative 3.9 → 3.12: **+17 node classes, −0, 3 field changes**; of the
113 classes present in both, **110 have byte-identical `_fields` — 97.3%**.
The three that moved each gained one optional field
(`FunctionDef`/`AsyncFunctionDef`/`ClassDef` gained `type_params`). **The
entire operator grammar is frozen across all four versions**, and the
expression grammar is frozen from 3.9 to 3.12.

**Corpus reach, stated honestly.** 121 corpus files touch 72 of the 81
census productions — 88.9%. So 100.00% value-identity is evidence about
*that* 89%, exercised 1458 times. It says nothing about `async`, `with`,
dict/set comprehensions, or — necessarily — about `match`, `TryStar`,
`TypeAlias` and t-strings, which cannot be evidenced by a corpus written
for 3.9.

**The finding that decides §2.4.** `PyErr` encodes zero-division as two
nullary constructors, with a docstring arguing that the split costs the
spec surface nothing — true, because CPython 3.9 has exactly two texts.
Measured: **3.11 and 3.12 split it three ways**, and 3.14 collapses it to
two rewritten ones. A 3.11 surface therefore needs a different
**constructor arity**, not a different string.

### 2.4 THE RULING: shared substrate, SIBLING editions

**Mechanism: the measured INTERSECTION lives once, in the version-neutral
layer; everything an edition decides lives WHOLE in that edition's own
directory. Editions are siblings. Neither is the base of the other, and
no definition takes a version parameter.**

The three mechanisms the charter was asked to price, and why each fails
as stated:

**Full per-version copies — refused, by both censuses.** For C it means
933 duplicated lines to carry one line of difference. For Python it means
duplicating `Semantics.lean`, `Runtime.lean` and 45 103 lines of
`Examples/` — the expensive half — to change 59 rows' worth of strings.
Worse than the volume: a bug fixed in one copy and not the other has no
mechanism that notices.

**Base + delta layering — refused, for a reason the Python census
supplies.** Layering privileges one edition as the base, which is false to
the subject (neither C17 nor C23 is derived from the other, and both are
still in use) and rots as editions accumulate: at N=4 nobody can read any
edition's surface without walking three overrides. And it provably cannot
express the delta that was measured — **you cannot override a DATATYPE's
constructor arity from a delta layer.** `PyErr`'s two zero-division
constructors are not a value to shadow; they are the type. Layering breaks
on the first real Python version delta anyone measured.

**Version-parameterized definitions — refused, on readability and on
scale.** `convert (ed : Edition) …` keeps one definition site, but every
theorem about C23 then carries an `ed = .c23` hypothesis, and the reader of
C23's arithmetic reads branches on editions they do not care about. It
also taxes what did not change: you would pay a version parameter on
`evalBinOp` to express that `+` is the same in every Python. At five
editions the arithmetic file is a switch statement.

**Why the ruling is not merely "layering renamed".** The shared layer is
*not an edition*. For Python the intersection is 3.9's semantics with the
message texts factored OUT — which is precisely what makes `PyErr`'s
arity problem dissolve rather than need a special case: the zero-division
constructors are measured NOT to be in the intersection, so they descend
into each edition's own layer and `Py39` states two while `Py311` states
three. The rule produces the right answer without being told about it.
And as editions are added the intersection is RE-MEASURED and may shrink,
pushing a rule down into every edition that has it — duplication that is
bounded by measurement rather than by an ordering chosen years earlier.

**What the reader gets, which was the requirement.** A reader holds one
edition's document and must read that edition's surface, whole. They do —
via the **clause manifest** (§5.5), which is per-edition, generated, and
checked: for edition E, clause X is realized by declaration D in module M,
and M is marked neutral (shared with editions Y, Z) or scoped. The whole
surface is the manifest's transitive closure; the *directory* carries only
the duplication the measurement justifies. A per-edition surface is a
generated VIEW, not a copied tree.

**And the duplication is policed by an instrument, not by discipline.**
The cross-edition gate runs over two manifests and reports, for every
clause both editions claim: identical (the neutral layer's claim holds),
deliberately different (with the change-list citation), or **silently
divergent — a defect**. That is the house census method applied to the
family's own source, and §2.5 is what happens without it.

### 2.5 What the instrument found in the tier that is founding the layout

The C tier models C23, and C23 moved 612 of 933 matched clause numbers
(§2.1). A C17-era number carried into a C23 document is therefore
plausible, silent and wrong — so the citations were checked. Found by
hand first; the hand is now replaced by **`harness/c_citation_check.py`**,
landed with this charter.

| citation | in the tree | C23's actual number | verdict |
| --- | --- | --- | --- |
| `Value.lean:157` — `<<` | "C23 §6.5.7" | **§6.5.8** (§6.5.7 is *Additive operators*) | C17's number, C23's label |
| `Value.lean:141` — truncating `/` | "§6.5.5" | **§6.5.6** (§6.5.5 is *Cast operators*) | C17's number, untagged |
| `c-semantics-design.md` §4.4 — sequencing | "5.1.2.3" | **5.1.2.4** *Program semantics* | C17's number |
| `c-tier-architecture.md` — compound literals | "C23 §6.5.2.5" | **does not exist in C23** | 6.5.2.x was restructured |
| `c-tier-architecture.md` — struct/union members | "C23 §6.5.2.3" | **does not exist in C23** | same |
| `Value.lean:68,178,221` — conversions | "C23 §6.3.1.3" | §6.3.1.3 | correct — and stable, see below |
| `c-semantics-design.md` §6 — `printf` | "C23 §7.23.6.1" | §7.23.6.1 | correct — C17's was 7.21.6.1 |

Nothing in the tree could have caught these: the numbers are plausible,
the titles are not written down beside them, and the drafts are not in the
repository and never will be. This is not a criticism of the C lane — it
is the strongest available argument that clause citations must be
**checked data** rather than prose, which is what §5.5 makes them. **The C
lane's retrofit is in flight and will move these rows**; the table records
the state at the commit that measured it, not a standing accusation.

**And the same instrument caught this document.** §1.3 originally read the
`§6.3.1.3` row above as evidence that C23 *mandates* two's-complement
conversion. It does not — p3 is identical across the editions and C23
J.3.6 (3) still lists it as implementation-defined. The corrected evidence
and the lesson are in §1.3. **The citation checker cannot catch that class
by itself**, and it says so: it proves a number RESOLVES in the claimed
edition, never that it is the number the author meant. `Value.lean:157`
resolves cleanly to *Additive operators* — only reading the surrounding
line reveals that the author meant shifts. **That gap is exactly the work
the clause manifest does**, and it is why §5.5 pairs a resolved citation
with the declaration it justifies rather than stopping at resolution.

**A fourth exclusion, found by running it.** The C lane's convention
(untagged inside `LeanModels/C/C23/` = C23; a superseded citation carries
its tag; a `docs/*.md` token means an internal reference) leaves one case
undefined, and it is noisy: these documents number their own sections
§1..§7, colliding with the standard's clauses 5, 6 and 7. Untagged `§5.2`,
`§5.4`, `§6.1` in the charter are internal cross-references, and resolving
them as ISO clauses produced four MISSING rows of pure noise — *correct
documentation reported as drift*, the exact failure the exclusions exist
to prevent. The rule the instrument adopts: **inside a `.md` file an
untagged `§` is an internal reference**; a `.lean` file has no section
structure, so untagged is unambiguous there. Untagged `.md` citations are
reported as `unclassified` rather than dropped, because that count — **12
today** — is the size of the convention's blind spot, and tagging them is
how it shrinks.

---

## 3 THE SHARED SUBSTRATE CONTRACT

### 3.1 What is shared today — measured, and it is one struct

* `LeanModels/Core/Basic.lean` is **13 lines** and defines `Span`.
* It is imported by **three** lane files: `Python/Ast.lean`, `C/Ast.lean`,
  `C/Value.lean` (plus the two umbrella modules).
* `Run σ α` is used by **Python (16 files) and SystemVerilog (3)**. C,
  RISC-V, Circuit, Spice and Verilog-A: zero.
* Re-derived today, and **grown since §L35 priced the move**: `Run.`
  appears **1282** times (was 1251), `: Run` **160** times (was 143),
  across **31** files (was 24).

**Everything else the C lane "reused" is METHOD, not code** — and the C
charter says so itself. That is not a failure; a method that transfers
entire is the most valuable thing this repository has. But it means the
substrate is one structure with two consumers, and a document that spoke
of it as an established platform would be describing something that does
not exist.

### 3.2 The list

**LANGUAGE-NEUTRAL — belongs in `LeanModels/Core/` or in the method:**

1. **`Run σ α`** — the four-constructor outcome covenant. State retained
   on `.ok`; `.timeout` is fuel exhaustion and nothing else; `.unsupported`
   is loud and fuel-independent. Measured parametric: `Run CWorld CVal`
   typechecks today.
2. **The ∃-fuel threshold form and `fuelMono`** — *"∃ n, ∀ fuel ≥ n, … =
   .ok …"*, induction on math variables never on fuel, side conditions by
   `omega`.
3. **`Span`** — subject to §3.5.
4. **The census / verdict / instrument METHOD** — census before pricing;
   the instrument lands beside the claim; double-run determinism; every
   refusal path RUN and not admired; no whitelist that silences a mismatch.
5. **The envelope discipline** — `schema_version`, `language`,
   **`language_version`** (§1.5), `frontend` FAMILY, `source_file`,
   `source_sha256`, `Unsupported` leaves for anything outside a pinned
   vocabulary, deterministic output, and a cache key that includes the
   profile.
6. **The batch protocol** — `jobs.jsonl`, ONE runner process for the whole
   batch, exactly one line per job in job order, a `runner-error` row
   rather than a missing row.
7. **The exit-code convention** 0/1/3/4/5, and the invariant that **3 and
   4 are never agreement**.
8. **Effects as world data, inputs as traces** — stdout is world data;
   clock, stdin, environment and argv are input traces with a loud
   underrun.
9. **The `maybe <name> <required-file> <cmd>` CI helper** — present ⇒ run,
   absent ⇒ SKIP, reported, never silently omitted.
10. **The coverage-by-clause tooling** (§5.5) — neutral SHAPE, per-language
    content.
11. **Component #1 — the monad and its verification-condition generator**
    (§3.4). One `SemM`, one `WPMonad` instance, the default `mvcgen`. No
    language writes a vcgen.
12. **Component #2 — SoftFloat** (§3.5). Layer 1 (executable bit-level
    IEEE 754) is supplied by core Lean on the pinned toolchain; layer 2
    (the round-of-exact spec algebra) is the family's build. Consumed by
    C, Wasm, SV, Python, Go — and **blocking** for ECMAScript.
13. **Component #3 — the concurrency pattern** (§3.6). Schedule as an
    explicit parameter, executable counterexample schedules, the DRF-SC
    fence, three proof-burden tiers. One pattern, one citation per
    language.

**PER-LANGUAGE — never shared, and the C tier measured why for the first
three:**

1. **Values.** C's integers have widths and a UB boundary across 327
   overflow-capable sites; Python's `RVal.int` is unbounded. One `Int`
   constructor cannot express "unsigned wraps, signed refuses" in adjacent
   operands, which `mix64` and `PACK_VM` require.
2. **Memory.** In C a local has an ADDRESS — 86 `&`-of-automatic and 20
   `&`-of-subobject sites — and `realloc` MOVES the hot table, so
   provenance is structural. Python's locals are bindings with no address
   and its `Addr := Nat` *is* an array index.
3. **The refusal taxonomy's causes.** Python's `.unsupported` is a
   property of the program TEXT and retires; C's UB refusal is a property
   of the RUN and never retires.
4. The AST, the ingester, the extractor, the oracle.

### 3.3 `Heap` is per-language, and the question is answered not deferred

The dispatch asked with a question mark. **The answer is no**, and the
evidence is that the two heaps in the tree disagree about something
fundamental: whether a local has an address. Python's `Heap := Array Obj`
with `Addr := Nat` cannot carry the provenance that says a `realloc`ed
pointer is dead; `Ptr = (Option ObjId, Int)` can. A neutral `Mem`
typeclass could be *invented*, and the charter's own rule forbids it:
share only what is ALREADY parametric, measured. `Run`'s σ was; a heap is
not, and a typeclass with two irreconcilable instances is a decoration.

### 3.4 ONE MONAD, ONE vcgen — the substrate's centerpiece

**The question: does every language need its own `mvcgen`? No.** Two
shared layers answer it, and the second is already on the pinned
toolchain.

**Layer 1 — one monad family.** Every interpreter in the family is a
state-threading, exception-carrying, fuel-indexed step function. Written
as such:

```lean
-- (illustrative — the substrate shape, not yet in the tree)
abbrev SemM (W : Type) (ρ : Type) := StateT W (ExceptT ρ Halt)
```

with `W` the language's World and `ρ` its error payload. `Run σ α` is
already this shape: σ is a genuine type parameter, `.ok`/`.exn` retain
state, and `.timeout`/`.unsupported` are the state-discarding halts. The C
tier reuses it verbatim — `Run CWorld CVal` typechecks against the existing
definition today — and that is the evidence, not a hope. SystemVerilog and
a future Go differ from Python only in `W`.

Two design constraints make this work and both are load-bearing:

* **Fuel stays OUT of the monad.** It is an index on the step function
  (`step : Nat → Stmt → SemM W ρ Unit`), not a reader layer, because
  `fuelMono` and the ∃-threshold form are theorems about the *family* of
  monadic programs indexed by fuel. Put fuel in the monad and every triple
  carries it.
* **Nondeterminism enters as an explicit PARAMETER**, per the ∀-resolution
  ruling — a schedule, an evaluation order, an entropy stream. The monad
  stays deterministic and the ∀ lives at theorem level. This is what keeps
  SystemVerilog's event regions and C's unspecified order expressible
  without changing the interpreter's type (§7.2 is what happens when it
  cannot be done).

Fuel monotonicity and the threshold form are then proved **once**, as
properties of the stack, instead of once per language.

**Layer 2 — the DEFAULT `mvcgen`, over one `WPMonad` instance.** Measured
on the pinned toolchain `leanprover/lean4:v4.33.0-rc1`: `Std.Do.Triple`,
`Std.Do.WP`, `Std.Do.WPMonad`, `Std.Do.PostShape`, `SPred`, `PostCond` and
the `mvcgen` tactic all resolve, and `Triple.pure` elaborates with its
`⦃P⦄ … ⦃Q⦄` notation. **No toolchain bump is required** — the caveat is
retired by measurement rather than left open. (The pilot must still show
mvcgen can *drive a real goal* here; existence and usability are different
claims.)

Per-language work under this scheme is then exactly: **the World type, the
error type, the primitive step functions, and `@[spec]` lemmas for the
primitives.** No language writes a vcgen.

**And none of this stratum is trusted (§0.1, principle II).** The monad is
part of the definition — it is how the interpreter is written — but the
vcgen, the `@[spec]` collection and every tactic over them are LIBRARY:
they search for proofs of statements the semantics fixed without them, the
kernel rechecks whatever they produce, and a gap in them is a gap to
report rather than a reason to restate a theorem.

**This formalizes existing practice; it does not discard it.** The Python
lane already has a hand-built triple layer — `PyTriple.call`,
`PyTriple.callsTo_ofRet`, `execStmts_append_run` — and its altitude lemmas
(`boolChain_and2`, `boolChain_and3`, `boolChain_and_falsy`, `compare_one`
in `Examples/python/sunfish/fold_depth1.lean`) ARE hand-made `Spec`
lemmas for primitives. `@[spec]` is already core Lean's mvcgen attribute
on this toolchain, and `Logic.lean` says so. The migration renames a
practice that was arrived at independently; that convergence is the
argument for it.

**Three caveats, stated because they are real.**

1. **Deep embedding.** `mvcgen` reasons about Lean programs in a monad.
   The interpreter is such a program, but its SUBJECT is an AST value, so
   the triples are about `exec stmt` for a symbolic `stmt` and the vcgen
   must unfold the interpreter's `match` on a **pinned** program literal —
   which is exactly what `py_simp`/`py_prove` do today, and why they work.
   The pilot validates this and nothing in this document assumes it.
2. **Toolchain.** Retired by measurement above. The pilot re-checks it
   rather than trusting this paragraph, because a bump would touch every
   lane.
3. **Python is MID-CAMPAIGN.** The prescription is asymmetric on purpose:
   **new tiers are monadic from day one; Python is BRIDGED** — adapter
   lemmas relating `PyTriple` to `Std.Do.Triple` — until the
   `RecursionStep` campaign closes. The retrofit is priced then, on the
   numbers of that day, and it is **never forced**. §3.6 applies the same
   trigger rule to `Run`.

A pilot lane is running the measured experiment concurrently. **Its report
is the evidence for this section and its numbers replace these
paragraphs' estimates**; nothing here should be read as a result.

### 3.5 SOFTFLOAT — shared component #2, and the premise it was deferred on is FALSE

**The correction first, because the record is wrong.** Three tier documents
defer floats as though the problem were the *specification*. It is not.
**IEEE 754's arithmetic core is the best-specified thing in this family** —
better specified than C's sequencing, better than SystemVerilog's event
regions, better than anything CPython documents. For `+ − × ÷ √` and the
comparisons, the standard names one correctly-rounded result for every
input, and computing it is **decidable integer arithmetic on finite
encodings**. There is nothing approximate about it.

**The obstacle was believed to be Lean-internal, and on the pinned
toolchain it no longer exists.** `docs/completeness.md` §6 records the
float rung as gated because *"Lean's `Float` is not kernel-reducible, so
`#py_check` and every captured `rfl` run would break on it — the same
family as the mergeSort trap."* Measured today on
`leanprover/lean4:v4.33.0-rc1`:

```
-- (illustrative — probes run against the pinned toolchain, not tree files)
structure Float where toModel : Float.Model
structure Float.Model where
  toBits : UInt64
  valid  : Float.Model.Format.binary64.Valid toBits.toBitVec
def Float.add : Float → Float → Float := fun a b => { toModel := a.toModel + b.toModel }
```

`Float` is a plain structure over a bit-level model and `Float.add` is a
plain Lean definition. Three theorems were kernel-checked to confirm that
this reduces, not merely elaborates:

* `total = 6.75` where `total` folds `(· + ·)` over a `List Float` —
  reduction through a library higher-order function;
* `sumTo 4 = 10.0` for a user-defined structurally recursive
  `Nat → Float` — reduction through the shape an interpreter has;
* `((0.1 : Float) + 0.2 == 0.30000000000000004) = true` — correct binary64
  rounding, which is the fact that matters.

All three depend on `[propext, Classical.choice, Quot.sound]` and nothing
else. **No `native_decide`, which stays banned.** Core ships **1856 lines**
of logical model under `Init/Data/Float/Model/` — a width-parametric
`Format` (`mantissaBitsWithoutImplicit`, `exponentBits`) with **both
`binary64` and `binary32`**, an unpacked representation, a rounding layer
whose `Accuracy` type encodes exactly "exact, or inexact and where the
infinitely precise value sits relative to the approximation plus half an
ulp", packing lemmas, and operations `Add Sub Mul Div Sqrt Compare Sign
Status OfNat OfScientific ToNat`. Its own header says it is *"part of the
logical model for floats which authors of float libraries need to rely
on."*

**So the component is not "write a softfloat". Layer 1 already exists.**

#### 3.5.1 The two layers

**Layer 1 — executable bit-level operations.** What interpreters observe.
Kernel-reducible, width-parametric, `binary32` and `binary64`. **Supplied
by core Lean on the pinned toolchain**; the family's work here is to
*depend on it deliberately* — pin the interface, gate the reduction
behaviour with `#guard`s the way every other tier gates its primitives, and
own the residue core does not cover.

**Layer 2 — the SPEC ALGEBRA, and this is what the family builds.**
Per-operation correctness, proved once, in IEEE form:

```
-- (illustrative — the obligation shape, not a tree file)
op_correct :  bitOp x y  =  round mode (exactRational (val x ∘ val y))
```

Downstream proofs then target **round-of-exact** and never our bit
algorithm. A SystemVerilog divider proof says "these output bits are the
correctly-rounded quotient", not "these output bits equal what
`Float.Model.div` computes" — the second is a tautology about an
implementation, the first is the theorem anyone wants.

**Why both layers are kernel-computable, which is the fact that makes this
tractable.** For `+ − × ÷ √` and `fma`, the **exact** result of finite
binary64 inputs is a **RATIONAL** number — sums, products and quotients of
dyadic rationals are rational, and `√` is decidable by comparing squares
rather than by computing a root. Rounding a rational to a format is finite
integer arithmetic on its numerator and denominator. **ℝ never appears.**
It enters only with the transcendentals, which is exactly why they are
deferred (§3.5.4) and exactly why deferring them costs the core nothing.

#### 3.5.2 The flagship theorem shape — cross-tier, in the family's own pattern

Thomas named the client: *proving a SystemVerilog circuit computes
floating-point division correctly.* That theorem factors the way the C
charter's twin-bridge theorem factors — **through a shared vertex, never as
a comparison of two models**:

> the SV tier runs the circuit and yields output BITS;
> SoftFloat layer 2 says what those bits must be — `round (exact quotient)`;
> the theorem is that the two agree, for all inputs in the claimed domain.

The circuit side is an ordinary SV-tier obligation; the specification side
is one `op_correct` instance; neither side knows about the other's
internals. This is the verified-FPU tradition — the AMD K5 divider and its
ACL2 lineage are the precedent, **cited and not vendored** — restated in
this family's shared-vertex pattern. Flocq is the corresponding precedent
for the layer-2 algebra itself, and likewise cited only.

**The circuit-side foothold, censused, because the obvious guess is
wrong.** `LeanModels/Circuit/` is **not** it. Measured: that lane imports
`Mathlib.Data.Real.Basic`, `Mathlib.Analysis.Calculus.Deriv.Basic` and
`Mathlib.MeasureTheory.*`, and its subject is `DCBlock`, natures,
disciplines, DC/AC/transient analysis and interval enclosures — it is the
**analog** lane, continuous-time physics over ℝ, and a floating-point
divider is a synchronous digital datapath. The two lanes share exactly one
edge in the whole tree: `Circuit/MixedSignal.lean` imports
`LeanModels.Sv.Surface`, which is the analog↔digital boundary and not a
shared circuit model. **The divider theorem's circuit side is the SV tier**
(`LeanModels/Sv/`, and the parametric `sv-0.2` layer in particular). A
founding lane that goes looking in `Circuit/` will find calculus.

#### 3.5.3 Consumers — and ECMAScript BLOCKS on this

| tier | need | consequence |
| --- | --- | --- |
| **ECMAScript** | its **only** number type is binary64 | **BLOCKING.** A float-free JS core slice is very nearly empty — no arithmetic, no array index arithmetic, no `length` comparison in its true type. The ES founding lane's charter must state SoftFloat as a **dependency**, not defer floats the way the Python lane could. |
| WebAssembly | `f32` and `f64` | needs the component **width-parametric**, which core's `Format` already is (`binary32` and `binary64` both present). Wasm is also where the NaN residue is specified rather than hand-waved (§3.5.4). |
| C | Annex F rung | unblocks the rung whose gate was "neither host declares `__STDC_IEC_60559_BFP__`" — that gate is about the *oracle's* conformance claim and stays; the *model's* half is answered here. |
| SystemVerilog | `real`, and the divider flagship | §3.5.2 |
| Python | `float`, `/`, `**` with negative exponent, `str`/`repr` of a float | the four grammar rows `docs/completeness.md` names, on a premise that has now moved. |
| Go | `float32`/`float64` | same component, no new work. |

#### 3.5.4 The genuinely unspecified residue routes to EXISTING machinery

Nothing here needs a new mechanism, and saying which mechanism is the
point:

* **NaN payload and sign** — genuinely unspecified by IEEE 754 for most
  operations. Routes to **∀-resolution** (§3.4's explicit-parameter
  design): the payload is a parameter, quantified at theorem level.
  WebAssembly is the exemplar because its specification *enumerates* the
  admissible NaN result patterns rather than leaving them to folklore, so
  the Wasm tier can state the ∀ precisely and the other tiers can copy the
  shape.
* **Excess precision and FP contraction** (`FLT_EVAL_METHOD`, fusing
  `a*b+c` into an fma) — these are **profile items**, exactly like
  `char_signed` and `sizeof(int)`: facts a host either provides or does
  not, pinned as a schema with a `#guard` per host and a loud rejection by
  name.
* **Transcendental accuracy** — C leaves it implementation-defined,
  ECMAScript calls it implementation-approximated. Routes to
  **REFUSE(`environment`)** — an unmodeled library function — or to a
  profile pin where a tier's oracle documents a bound. It never routes to
  an invented answer, and it is the only place ℝ would be needed.

#### 3.5.5 The price, honestly

Layer 1 is **free on the pinned toolchain** and its cost is a pin plus
gates. Layer 2 is the build, and it has a natural order:

1. **Base operations and comparisons** — `+ − × ÷ √`, the six comparison
   predicates, and the exact-rational bridge they all share. This is the
   component; everything below is a widening.
2. **Conversions** — integer↔float both directions, and the format
   conversions `binary32 ↔ binary64` Wasm needs.
3. **Decimal parsing and printing — its own sub-inch, and larger than it
   looks.** Correctly-rounded decimal↔binary conversion is a real
   algorithm, and it is where `printf`'s `%f` lives. The C tier's own
   census says float conversions are 21% of c-testsuite's format specs and
   10% of Fujitsu's, so this sub-inch is what unblocks that slice — and
   nothing before it needs it.
4. **`fma`** — one more correctly-rounded operation, same shape as (1),
   and the one C's contraction question resolves against.
5. **Transcendentals — LAST, and only per-tier need.** They are the only
   part that leaves the rationals, and no tier in the family has
   demonstrated a need for them.

**A build lane is commissioned on this plan.** Its first deliverable is
step 1's census in the family's own pattern (§5.4): which operations each
existing tier's corpus actually reaches, measured, before any Lean.

**And the stale record is corrected in three places.** The claim in
`docs/completeness.md` §6, and the float deferrals in
`docs/c-semantics-design.md` §1.3 and `docs/c23-goal.md` §5.3, were
correct when written and are now correct only about their *oracle-side*
halves. The Lean-side premise is measurably false on the pinned toolchain.
Whether a tier's oracle declares Annex F is still a real question; whether
Lean can compute a correctly-rounded sum in the kernel is no longer one.

### 3.6 CONCURRENCY — the four-piece pattern, and it is the ∀-parameter ruling at scale

The goal, stated by Thomas: *prove a multithreaded C program correct for
**all** possible interleavings — and where it is not correct, be unable to
prove it AND able to exhibit a counterexample.* That is not a misfit. It is
§3.4's explicit-parameter design at a larger scale, and it needs no new
architecture. Four pieces.

**(1) INTERLEAVING SEMANTICS — the schedule is a parameter.** A schedule is
an explicit input: a thread-choice stream, exactly the shape §3.5.4 gives
a NaN payload and §6.2 gives an entropy stream. The interpreter is
**deterministic per (program, schedule)**, so `SemM`, `fuelMono`, the
∃-fuel threshold form and `mvcgen` are all untouched — a threaded step
function is `sched → Nat → SemM W ρ α`, and nothing about the monad
changes. Correctness is then the ordinary shape:

    ∀ schedule, the run under that schedule satisfies the spec

The ∀ lives at theorem level, where this family already puts every
resolution of nondeterminism.

**(2) THE COUNTEREXAMPLE IS FIRST-CLASS, and this is a capability worth
naming.** Because the interpreter is deterministic per schedule, a
violation witness is a **finite, concrete schedule** — and it is checked
by *running* it:

```
-- (illustrative — the witness shape, not a tree file)
#guard (run prog badSchedule fuel).observable == theWrongAnswer
```

A kernel-checked, executable counterexample. This is the house law —
*every refusal path RUN, not admired* — applied to bug-finding rather than
to instruments. **Failure to prove correctness comes WITH an exhibitable
breaking interleaving**, which is precisely the asymmetry Thomas asked
for: the artifact cannot be talked into a proof, and when it declines it
says why in a form a human can replay.

This is **§0.1's exit (a)** made concrete, and it is the reason the
doctrine's third principle is constructive rather than a shrug: when a
proof does not come, the framework's first move is to try to hand back a
run that shows why it should not have.

**(3) THE DRF-SC FENCE, spec-mirrored — the standard's own clause carries
the bridge.** Full C11/C23 atomics exceed interleaving semantics: relaxed
and acquire-release orderings admit behaviors no interleaving generates.
The bridge is in the standard, and the citations below were **verified
against N3220 by the §2.1 instrument** rather than quoted:

* **C23 §5.1.2.5 ¶35** defines a data race — two conflicting actions in
  different threads, at least one non-atomic, neither happening before the
  other — and states that any such race **results in undefined behavior**.
* **C23 §5.1.2.5 NOTE 18** states the DRF-SC guarantee in the standard's
  own words: programs that prevent all data races using simple mutexes and
  `memory_order_seq_cst` operations, and no other synchronization, behave
  **as though their threads' operations were simply interleaved**, each
  value computation reading the last value stored in that interleaving —
  *"normally referred to as sequential consistency"* — and this **applies
  only to data-race-free programs**.
* **C23 Annex J.2 item (5)** indexes it: *"The execution of a program
  contains a data race (5.1.2.5)."* — so the refusal is J.2-numbered, and
  §2.1's finding that C23 numbered its UB list pays off here concretely.
* The coherence and ordering requirements the guarantee rests on are
  **§7.17.3 *Order and consistency***, whose number is stable across C17
  and C23 (verified — one of the minority that did not move).

**One honesty note, because it is load-bearing.** NOTE 18 is a NOTE, and
notes are informative rather than normative in ISO drafting. The
*normative* basis is ¶35's UB-on-race plus §7.17.3's ordering rules; the
note states the consequence. A tier that cites the note as if it were
normative would be making exactly the kind of overclaim §2.5 caught.

**What this buys.** DRF itself has a theorem-friendly interleaving
characterization — a program has a race iff there is an SC execution in
which two conflicting cross-thread accesses are adjacent — which is a
∀-schedule statement in our own terms, provable by the machinery of piece
(1). So: **the axiomatic model stays OUTSIDE the artifact, and the
standard's own clause is what lets it stay outside.** A racy program is UB,
which is REFUSE(`undefined`) indexed at J.2 (5) — **with the witness
schedule attached**, per piece (2). The refusal is not a shrug; it is a
bug report.

**(4) PROOF-BURDEN TIERS — three, and the default is the cheap one. All
three are LIBRARY, none is semantics (§0.1, principle II).** Piece (1)
fixed what correctness MEANS, quantified over every schedule; these are
three ways to find a proof of it. None of them may narrow the ∀, and their
incompleteness is expected rather than concealed.

| burden | method | analogue already in the tree |
| --- | --- | --- |
| **bounded fixture** | ∀-schedule is **DECIDABLE** by exhaustive exploration of the finite schedule space, checked as a battery | the census-battery pattern (§5.4) |
| **general theorem** | commutativity / **mover** lemmas (Lipton's reduction): show adjacent steps commute, collapse the schedule space | the concurrency analogue of `@[spec]` and the altitude lemmas (§3.4) |
| **heavy artillery** | ownership / separation-logic (Iris-style) reasoning | **named, not the default** — reached for only when movers fail |

The first tier is the important one: for a bounded fixture, "correct for
all interleavings" is a *computation*, not a proof, and it lands as a
`#guard` battery on day one.

**UNIFICATION — Go and C-threads are ONE pattern with two citations.** Go's
memory model is explicitly DRF-SC, so a Go tier and a future C-threads
extension share pieces (1), (2) and (4) verbatim and differ only in which
document supplies piece (3). Building either builds most of the other, and
a lane founding one should say so in its charter.

**THE RESIDUAL TRUE MISFIT, narrowed to one sentence.** What remains
genuinely outside is **verifying the relaxed-atomics fragment itself** —
reasoning about programs that deliberately use `memory_order_relaxed` or
acquire-release beyond what DRF-SC covers. Those behaviors are defined by
axioms over execution graphs rather than generated by any schedule, so the
"parameter" would be the graph, and the artifact would become a
consistency CHECKER — a different architecture (§6.1).

### 3.7 `Span` — the ruling on three shapes

Measured, three span types for seven lanes:

| type | shape | lanes |
| --- | --- | --- |
| `LeanModels.Span` | 4 fields: `lineno`, `colOffset`, `endLineno`, `endColOffset` | Python, C |
| `LeanModels.VerilogA.Span` | 2 fields: `line`, `column := 1` | Verilog-A |
| `LeanModels.Circuit.Spice.SourceSpan` | 1 field: `line` | Circuit, Spice |

And the "language-neutral" one is not neutral: its own docstring says the
field names *mirror CPython's `ast` attributes*. A C span is a clang span
wearing CPython's field names.

**Ruling.** `Span` stays in `Core` and is the family's span, with the
docstring corrected to state the *contract* (1-based lines, 0-based
columns, exclusive ends) rather than its Python provenance. The two
divergent types are **not** defects to be merged on sight: Verilog-A and
SPICE genuinely observe less (a line, or a line and a column), and
widening them would manufacture end positions their frontends do not
report. The rule is therefore

> a lane MAY narrow the family span to the positions its frontend
> actually reports, and MUST NOT re-declare a type with the same name at
> a different shape.

`VerilogA.Span` violates the second half — same name, different shape, in
a sibling namespace — and is renamed when that lane is next open. The C
envelope's two-location spans (spelling and expansion, forced by six
function-like macros) are the model for how a lane EXTENDS rather than
redeclares.

### 3.8 `Run`'s move to `Core` — deferral CONFIRMED, trigger FIXED

`docs/c-tier-charter.md` §2.4 priced the move and deferred it. The
deferral is confirmed and two things about it are made concrete, because
"later" is not a trigger.

**Destination:** `LeanModels/Core/Outcome.lean`, with
`LeanModels/Python/Runtime.lean` re-exporting so no Python call site
changes.

**Trigger:** the inch that gives `Run` its **second consumer with a
world** — C's M2 inch 4 (statements + `CWorld`). Not before, because the
ingester tier does not mention `Run`; not after, because the standing
prohibition is that a C interpreter landing with its own copy of `Run` is
a defect and not a design.

**And the price is drifting.** §L35 measured 1251 `Run.` sites in 24
files; today it is **1282 in 31**. The deferral is correct and it is not
free, which is precisely why the trigger is now a named inch rather than
a judgement call.

The `Run.exn` payload decision (`Run σ ε α`, or C's terminal riding in α)
belongs to the same inch. It is the one place the outcome type is not yet
neutral, and naming it here is cheaper than discovering it there.

---

## 4 THE AUTHORITY TAXONOMY

### 4.1 Two authorities, and a tier declares which it is

**SPEC-MIRROR.** A published normative document defines the language. The
model's obligation is **clause coverage**: every clause the tier claims is
realized by a declaration, and the manifest says which. C, SystemVerilog,
WebAssembly, ECMAScript, Ada, RISC-V.

**INTERPRETER-EXTRACTION.** No normative document is the authority in
practice. The model's obligation is **differential agreement**, and the
differential harness IS the extraction instrument. Python, SPICE,
Verilog-A.

The distinction is about where a rule comes from, not about rigor. The
Python lane's `docs/completeness.md` §5 records five grammar verdicts read
off the source and MEASURED otherwise — four of them became the cheapest
rung on its ladder. Under extraction, `print(5 ^ 3)` outranks any reading.

### 4.2 The precedence rule where BOTH exist

Most spec languages also have a dominant implementation, and every tier in
this family that mirrors a spec also runs one: C targets ISO 9899 and runs
clang; SystemVerilog targets IEEE 1800 and runs pyslang plus a simulator;
Wasm, ECMAScript and Ada all have reference implementations.

> **The SPEC is the target. The IMPLEMENTATION is the oracle for the
> suite's expected outputs. A divergence between them is a FINDING — it is
> recorded with both citations, and it blocks neither side.**

Concretely: the model's rules cite the spec's clauses; the harness's
expected values come from the reference implementation; MATCH means the
model agreed with the implementation; a manifest row means the model
states the spec's rule. When they disagree — the implementation does X,
the spec says Y — **the model states Y, the harness records that the
oracle does X, and the row is published as a divergence finding.** Neither
side is silently adjusted, and neither is "fixed" to make a scoreboard
green.

The tree already contains the benign instance: the C tier's `-std=c23` pin
on `VM_VAL`'s conversion, where the spec MANDATES what an earlier edition
left implementation-defined and both development hosts happen to do the
mandated thing. The unbenign instance is §1.5's SV row — a lane citing one
edition and measuring against another's corpus, with no field that could
have said so.

**Where the spec is silent or ambiguous: REFUSE.** The model never invents
a rule the document does not state and the oracle merely happens to
exhibit. The single exception is the unspecified-order class, which gets
the canonical-plus-census treatment already recorded (§5.2, cause 4).

### 4.3 The behavior-classes → refusal-taxonomy mapping slot

Every spec-mirror tier fills this table before it writes semantics. C's
row is filled; the rest are the founding lanes' first deliverable.

| tier | the spec's behavior classes | mapping |
| --- | --- | --- |
| **C** | undefined; unspecified; implementation-defined; locale-specific; constraint violation | UB → REFUSE(`undefined`), never retires, 11 classes armed, J.2-shaped. Unspecified order → canonical left-to-right + census, REFUSE where the census cannot show it unobservable (20 residual sites). Implementation-defined → PINNED by the profile schema; a host that disagrees is rejected by name. Constraint violation → the frontend rejects, phases 1–6 being outside Lean. |
| **SystemVerilog** | "shall be an error"; implementation-dependent; and a large SCHEDULING nondeterminism class (the event regions) | **PROPOSED.** The event regions are cause 4's natural home; the schedule is the explicit parameter of §3.4. |
| **WebAssembly** | deterministic by design, with a small NAMED nondeterminism set (NaN payloads, resource exhaustion, host behavior); traps are DEFINED outcomes, not UB | **PROPOSED.** Expect cause 2 to be nearly EMPTY, and gate that: a Wasm tier emitting `undefined` has a bug. This is the family's best case and worth founding early for exactly that reason — it calibrates the instrument against a language where coverage can be near-exact. |
| **ECMAScript** | implementation-defined / implementation-approximated (locale, `Date`, `Math`); host hooks | **PROPOSED.** The spec is ALGORITHMIC — numbered abstract-operation steps — so the mirror is per abstract operation and coverage is per step, not per prose clause. §5.5's manifest is written to allow this. |
| **Ada** | bounded error; erroneous execution; unspecified; implementation-defined | **PROPOSED.** The finest taxonomy in the family and the best fit for REFUSE-with-a-cause. Ada is the stress test of whether four causes are enough; if a fifth is needed, Ada is where it will show. |

**Extraction tiers have no such table, and that is the point.** Their
behavior classes are whatever the census DISCOVERS, not what a document
enumerates — Python's are hash order, live dict mutation, stateful
generator drain, boundary observation forms, and they were found by
running programs. That is why `docs/completeness.md`'s class list is
measured and `docs/c23-goal.md`'s is derived.

---

## 5 THE VERDICT AND SCOREBOARD SYSTEM

One scoreboard shape for the whole family. The invariant is unchanged and
is the whole point: **DIVERGE must be zero, and REFUSE is never
agreement.**

### 5.1 The verdicts

| verdict | meaning |
| --- | --- |
| **MATCH** | the model ran to completion and its observable equals the suite's expectation |
| **REFUSE** | the model declined, loudly and fuel-independently. FOUR disjoint causes (§5.2), reported separately |
| **DIVERGE** | the model produced an observable and it DISAGREES. The invariant violation. Zero, always |
| **TIMEOUT** | fuel exhausted. The only exhaustion outcome; never conflated with REFUSE |

### 5.2 REFUSE has FOUR causes, and the fourth is a finding

They retire on completely different schedules, so pooling them makes the
scoreboard unreadable.

1. **`unsupported` — out-of-tier construct.** Retires by climbing a rung.
   Universal; Python's `.unsupported` exactly.
2. **`undefined` — the language says this run has no meaning.** C's UB,
   Ada's erroneous execution. **Never retires: it is the product.** Its
   presence is a per-language FACT — Python has no UB, and a
   deterministic-by-design language's bucket should be near-empty and
   gated as such.
3. **`environment` — the run needs something outside the modeled slice.**
   Unmodeled libc, an unprovided host import, an unmodeled builtin.
   Retires by widening the slice. (C's taxonomy calls this `libc`, which
   is too C-specific a name for a family contract.)
4. **`order-dependence` — the language admits several orders and the
   model cannot show the observable invariant under all of them.**

**Cause 4 is new at the family level, and the C tier is the evidence that
it is needed.** `docs/c-semantics-design.md` §3.1 fixes three causes;
§4.4 then rules "REFUSE where a static census cannot show the order
unobservable" for the 20 residual may-alias sites. That refusal fits none
of the three: the construct is in the vocabulary (not cause 1), the
program is *unspecified*-dependent rather than undefined (not cause 2 —
unsequenced modification is UB, but which argument evaluates first is
not), and nothing is missing from the slice (not cause 3). Python's twelve
hash-order refusals and its permanently-loud same-size key-set regime are
the same cause, arrived at from the other authority. SystemVerilog's event
regions will be its largest bucket.

**Why it is a REFUSAL cause and not a fifth verdict.** A refusal is what
the model actually emits today, on both boards. The alternative — a
genuine ORDER-DEPENDENT verdict meaning "the model ran, and the answer is
order-sensitive" — requires the model to enumerate the admissible orders
and show the observable invariant. That is a different and much larger
obligation, it is the honest home of §3.4's explicit-parameter design, and
it is named here as a priced fork rather than taken.

### 5.3 VACUOUS is not a verdict

A run that executed **nothing** must never score as agreement. Python's
harness carries `"live"`; C's scoreboard carries the statement count. This
is an instrument-level ERROR, not a verdict — a scoreboard that reports it
as MATCH is broken, and one that reports it as REFUSE is lying about
coverage.

### 5.4 One census-instrument pattern per tier

`harness/c_construct_census.py` fixed the contract; every tier's
instrument copies it:

* named `harness/<lang>_<subject>_census.py`, output to
  `docs/<lang>-<subject>-census.json`, sorted and machine-readable;
* a **`--compare`** mode against the committed JSON, because corpora that
  live in other repositories move on their own schedule and staleness must
  be mechanically detectable rather than merely possible;
* **every refusal path RUN, not admired** — a missing input, a zero-row
  parse (an empty census is an instrument fault, never a finding), and a
  rejected input. The third one was a real defect in the C instrument,
  found only by executing the fixture, and this charter's own instrument
  reproduced the lesson: its first answer was a plausible table produced
  by matching renumbered clauses (§2.1), and it was the spot-checks that
  caught it;
* **double-run byte-identical**, verified;
* it stamps the frontend FAMILY and the profile, because both are INPUTS
  to the result and not decoration;
* **not wired into CI when its corpus is out-of-tree** — a gate that is a
  permanent SKIP is a check pretending. `maybe` is where it belongs once
  the corpus is in-tree.

### 5.5 Coverage by clause — the manifest

Where a spec exists, the tier maintains **one manifest per (language,
edition)**:

    docs/<lang>-<ver>-clause-manifest.json

One row per clause the tier CLAIMS:

    clause        the edition's own number
    title         the edition's own title, verbatim
    status        stated | refused | out-of-tier | not-applicable
    declarations  the Lean declarations that realize it
    gates         the #guard / battery rows that check it
    layer         neutral | scoped        (which directory it lives in)

Coverage is `stated / (stated + refused + out-of-tier)`. It is
**generated and checked, never hand-maintained** — the tree already
demonstrates why (§2.5: three of five hand-written citations were an
edition out of date). For an algorithmic spec like ECMAScript's, `clause`
is the abstract operation and its step number; the shape is unchanged.

The manifest is the single artifact that serves three of this charter's
deliverables at once, which is why it is worth its cost: it is the
per-edition **reader's view** promised in §2.4, the **cross-edition diff
gate** that polices the neutral layer, and the **coverage-by-clause**
scoreboard. It starts at ~30 rows for C23's value layer and grows with the
tier.

---

## 6 LIMITS — the languages this model does NOT fit

Tier selection stays principled only if the model's assumptions are
written down. Five assumptions, then the misfits.

**Read this section against §0.1, because the doctrine fixes what "does
not fit" may mean.** A misfit is **never** "hard to prove" — hardness is
expected, is accepted at the definition layer, and is a signal to the
program rather than to the model (principle III). A misfit is strictly
narrower: a subject whose correctness this architecture **cannot DEFINE**
soundly and completely, because its behaviors are not generated by an
interpreter over explicit parameters. Every entry below fails at that
layer, not at the proof layer. That is why the concurrency entry shrank to
the relaxed-atomics fragment (§3.6) and why floats left the list entirely
(§3.5): in both cases the definition was available, and only the folklore
said otherwise.

**The model assumes:** (1) execution proceeds in **discrete steps**; (2)
the observable state is **finitely representable**; (3) behavior is
**GENERATED by an interpreter** that is deterministic modulo explicit
parameters; (4) per-run claims are **quantified over those parameters**;
(5) observation is **termination-indexed** — the ∃-fuel threshold form
needs a final answer to index.

### 6.1 The misfits

1. **THE RELAXED-ATOMICS FRAGMENT ITSELF** — and note how narrow this now
   is. **Concurrency is NOT a misfit**: §3.6 gives it a four-piece pattern
   — schedule-as-parameter, executable counterexample schedules, the
   standard's own DRF-SC clause as the fence, and three proof-burden tiers
   — under which "correct for all interleavings" is an ordinary
   ∀-parameter theorem and, on a bounded fixture, a decidable one. What
   stays outside is only the fragment *beyond* DRF: programs deliberately
   using `memory_order_relaxed` or acquire-release, whose allowed
   behaviors are the execution GRAPHS satisfying a set of axioms rather
   than the traces any schedule generates. Load-buffering and
   out-of-thin-air outcomes have no generating schedule; the "parameter"
   would be the graph, and the artifact would become a **consistency
   CHECKER** — a different architecture. `docs/c-tier-charter.md` §3.3
   measured the cost of trying: R6 "is the one rung that is not a
   widening", replacing a state function with a memory-ORDER relation and
   breaking `fuelMono`, kernel-reducibility and the one-line-per-job batch
   protocol at once. That verdict survives, scoped to the fragment that
   earns it.
2. **PRODUCTIVE NON-TERMINATION** — streams, servers, reactive systems,
   lazy infinite structures. There is no final answer for ∃-fuel to index.
   The known extension is **observation-indexed** theorems: fuel indexes
   the output PREFIX and bisimulation replaces termination. Lustre-style
   per-tick systems fit today, which is why the SystemVerilog lane works
   per cycle. The verdict system's termination assumption is hereby
   written down rather than assumed.
3. **CONTINUOUS STATE** — Verilog-AMS, Modelica, hybrid systems: worlds
   evolving by ODEs over ℝ. Outside the `Run σ` model, and the tree
   already says so by building them differently: `LeanModels/Circuit/` and
   `LeanModels/Spice/` are 27 675 lines that use no `Run` at all,
   modelling by interval enclosure and contract (`Circuit/Enclosure.lean`
   quantifies over `ℝ` directly). That is not a lane to convert; it is a
   second architecture in the same repository, correctly.
4. **DISTRIBUTIONAL CLAIMS** — probabilistic and quantum programs. A
   **half-fit, stated honestly**: per-seed determinism fits perfectly via
   an entropy-stream parameter, and the verdict system would score it. But
   the interesting theorems are about the distribution OVER seeds, and
   that needs a measure layer the scoreboard does not have. Per-seed
   claims are in reach; distributional ones are not.
5. **TRANSCENDENTAL FUNCTIONS over ℝ** — and note carefully that this is
   *not* "floats". Floats are **not** a misfit and not a tax: IEEE 754's
   arithmetic core is the best-specified subject in the family, its
   correctly-rounded results are decidable integer arithmetic on finite
   encodings, and it is a shared COMPONENT (§3.5), not a limit. What
   genuinely sits outside is the part that leaves the rationals — `sin`,
   `exp`, `log` and their accuracy claims, where C says
   implementation-defined and ECMAScript says implementation-approximated.
   Those route to REFUSE(`environment`) or to a profile pin (§3.5.4); they
   are the *only* float-adjacent thing that would need ℝ, and no tier has
   demonstrated a need for them.

### 6.2 The deceptive fits, for contrast

* **Go** — looks like a concurrency misfit, is not: its memory model is
  explicitly DRF-SC, so schedules GENERATE its behavior and §3.6's four
  pieces apply unchanged. Go and a future C-threads extension are one
  pattern with two spec citations.
* **Prolog** — looks nondeterministic, is not: ISO fixes depth-first
  search with leftmost selection, so the interpreter is deterministic and
  the tier is ordinary.
* **SQL** — bag semantics, and row order is precisely the ∀-resolution
  pattern of §3.4: an explicit parameter, quantified at theorem level.
* **Interactive programs** — the input stream is a parameter, which is
  what the family already does with stdin, the clock, the environment and
  argv.
* **C++ and Rust** — the model fits them fine. Their problems are scale
  and, for Rust, the absence of a normative spec to mirror; neither is an
  architectural misfit, and neither should be founded on the strength of
  "it fits".

---

## 7 COORDINATION LAW — many lanes, one machine, one master

A family of tiers means a family of lanes, and they share two scarce
resources. The rules below are **standing law for every lane**, and this
section owns them.

### 7.1 The machine-wide BUILD LOCK (mandatory, 2026-08-22)

Concurrent Lean builds took the development machine down — load 29 across
41 processes. The protocol:

1. **ONE full build at a time, machine-wide.** Before any `lake build`, any
   triad run, or any `lake env lean` on a file that triggers more than ~100
   jobs, acquire the lock — an `mkdir` spinlock, which is portable on
   macOS where `flock` is not:

   ```
   while ! mkdir /tmp/ls-build.lock 2>/dev/null; do sleep 60; done
   trap 'rmdir /tmp/ls-build.lock' EXIT
   ```

   Release promptly. **Never hold it while thinking or editing.**
2. **Cap parallelism even under the lock**: `lake build -j4`.
3. **Scratch-file loops** — `lake env lean` on small dependency-free files
   — are allowed WITHOUT the lock, but must run under `nice -n 19` and
   stay small.
4. **Batch aggressively: one triad per landing, never per edit.**
   Stage, then build. No speculative builds.
5. **A stale lock** (left by a dead lane) is cleared only after verifying
   by parentage and cwd that no build is running — then `rmdir` and note
   it.
6. **Never kill another lane's processes.** Kills by parentage only. The
   owner's own tooling is not yours, and this has been got wrong twice.

The reason this belongs in the architecture document rather than in a
lane's notes: the family's whole shape — many tiers, each with its own
corpus and its own triad — is what creates the contention. A convention
that makes founding five lanes cheap has to say how five lanes share one
build.

### 7.2 The master branch

Many lanes push the same master. Fetch-rebase before every push; read your
own backlog section at push time rather than at draft time, because the
section number you reserved may have been taken while you worked. After
any rebase that touches `.lean`, re-run the build and the differential
before pushing — a rebase is a merge, and a merge is not a measurement.

---

## 8 THE FOUNDING CHECKLIST

The order below is the C lane's measured order, which worked: M1 landed in
seven inches over roughly two sessions, endgame-neutral by construction. A
founding lane produces these in this sequence, and **no step's claim is
real until an instrument re-derives it.**

0. **The registry row** (§1.2) — tag, edition tokens, authority, oracle,
   corpus, and **state (founding vs consolidation)**. Proposed until step 1
   ratifies it.

   **The corpus entry carries its LICENSE and PROVENANCE, at this step and
   not later.** Twice now the answer changed the corpus: the C tier's
   219 `.otag` files split c-testsuite into an ISC half and an LGPL half,
   and the SV corpus turned out to be unlicensed, privately provenanced,
   and to **vendor the very standard it tests against** (§1.2). A corpus
   that fails either test is disqualified before a line is written, and
   "we can sort the licensing out later" is how a repository acquires
   something it cannot ship.
1. **The construct CENSUS and its instrument**, on a real corpus, to the
   §5.4 contract.
2. **The AUTHORITY declaration** — the spec document and edition, or the
   reference implementation and release line; where both exist, the §4.2
   precedence statement; and for a spec tier, the §4.3 mapping table.
3. **The PROFILE** — the implementation-defined facts the corpus depends
   on, as a schema every host must satisfy, with a stop-condition if two
   hosts disagree. Not a pinned machine: the C lane's question dissolved
   when it stopped anointing one.
4. **The ENVELOPE schema** — `language_version` first-class (§1.5), the
   node vocabulary DERIVED from step 1's census rather than chosen, and a
   check that the two cannot drift.
5. **The extractor** — one per language (§1.6), all three refusal paths
   RUN.
6. **`LeanModels/<Lang>/`** — the AST, the ingester, and structural
   `#guard`s the census independently knows. No semantics.
7. **`LeanModels/<Lang>/<Ver>/`** — the semantics, and the manifest
   (§5.5) starting the same day.

---

## 9 WHAT THIS DOCUMENT DOES NOT DECIDE

* **Whether any of the three new spec tiers is founded, or in what
  order.** The registry rows are PROPOSED and §4.3's observation that
  WebAssembly is the family's best calibration case is an argument, not a
  schedule.
* **The monad migration's numbers.** §3.4 states the design and retires
  the toolchain caveat by measurement; the pilot lane's report is the
  evidence, and Python's retrofit is priced when its campaign closes and
  never forced.
* **Whether `Run` moves at C's M2 inch 4 or the inch slips.** The trigger
  is fixed (§3.6); the inch is the C lane's.
* **The C lane's three stale citations** (§2.5). Found here, fixed there.
* **`VerilogA.Span`'s rename** (§3.5) — when that lane is next open.
* **`extractors/sv/census.py`'s move** into `harness/` (§1.6) — likewise.
* **SoftFloat's layer-2 build.** §3.5 states the design, corrects the
  premise by measurement and prices the order; the commissioned build
  lane's census is the evidence, and its first step is a corpus census,
  not Lean.
* **Whether any tier's ORACLE declares Annex F.** Unchanged, and still a
  named Thomas-decision. §3.5 answers the Lean-side half only.

---

## 10 WHAT LANDED WITH THIS CHARTER

* **`docs/family-architecture.md`** — this document.
* **`harness/c_clause_delta.py`** — the C17→C23 clause instrument (§2.1).
  Matches on the ancestor-title path because C23 renumbered 6.5, 6.8 and
  5.1.2 wholesale; rescues parent-retitled clauses by title; flags
  heading-only rows `thin` and excludes them from ratio statistics;
  refuses loudly on a missing input, a zero-clause parse and an
  implausible count; byte-identical on a re-run, verified.
* **`docs/c17-c23-clause-delta.json`** — its output, **aggregates plus the
  clauses the C tier cites**. The full 1330-row table is deliberately NOT
  committed: it would be a rendering of the standard's own contents, and
  **no ISO text is vendored in this repository**. Anyone with the public
  drafts re-runs the instrument for the whole table.
* **`harness/c_citation_check.py`** — resolves every ISO citation in the C
  tier against the drafts and reports what the cited clause is actually
  TITLED in the edition claimed (§2.5). Implements the C lane's citation
  convention plus the fourth exclusion this instrument's own run
  discovered; verdicts `ok` / `MISSING` / `AMBIGUOUS`; exits non-zero on
  any problem; refuses loudly when a draft is absent and when it finds
  zero citations. Deterministic, verified. **Its output is deliberately
  NOT committed**: the C lane's retrofit is in flight, so a checked-in
  baseline would be stale within the day and would invite the "fixed
  documentation reports as drift" failure it exists to prevent. The
  instrument is the durable artifact; its output is a live check.
* **`harness/py_version_delta.py`** — the Python version instrument
  (§2.3), in two halves: the `ast` grammar per interpreter, and the
  whole-program corpus executed under each. Missing interpreters are
  reported and skipped loudly; a row it cannot run is an ERROR row with a
  reason. Deterministic, verified.
* **`docs/py-version-delta.json`** — its output across CPython
  3.9.19 / 3.11.11 / 3.12.8 / 3.14.5. 65 script rows, 0 error rows.
* **`docs/backlog.md`** — the record.

**The fuller closed-function measurement is cited and not landed here.**
The 1458-row run behind §2.3's 100.00% value-identity extends
`harness/diff_test.py`'s comparison to exception MESSAGE text, which the
harness does not currently compare — the closed-function surface compares
exception CLASSES only, so today the entire 59-row message delta is
invisible to `harness/cases.json`. **That is an owed item for the Python
lane**, and it matters precisely because §2.4 puts the message renderer in
the version-scoped layer: if the delta layer is a renderer, the cases
surface has to start comparing what the renderer produces, or the layer's
whole cost centre stays unmeasured.

**This charter carries no Lean.** It changes `docs/` and adds two
`harness/` instruments, and it touches no `.lean` file, no `lakefile.toml`,
no `LeanModels.lean` and no `lean-toolchain` — by design, because the
document constrains and the lanes implement. `docs_check` is therefore the
relevant gate and it is green at 73/73 with 19 illustrative-exempt. The
machine was at load 22 under other lanes' builds while this landed, so per
§7.1 no build was started for a change that contains no Lean; the probes
that produced §3.4's and §3.5's toolchain measurements were small
dependency-free scratch files run under `nice -n 19`, which §7.1 rule 3
permits without the lock.
