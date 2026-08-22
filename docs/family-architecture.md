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

The library grows **by demand**, and §5.6 gives that clause its selection
rule: the demand comes from **one theorem-worthy exemplar per tier**,
because a library gap is invisible to anything that never asks the library
for a proof — and suite scoring never does.

#### II(a) DECISION PROCEDURES — a graded policy, not a ban

Thomas's ruling: he is *not principally against* `bv_decide` and
`native_decide`. The objections are **performance** — 64- and 128-bit goals
blow up — and **informativeness**: *"a symbolic proof works for all bit
widths."* So the family **supports** these operations and **discourages
overusing** them, which is a preference ladder rather than a prohibition.

**THE PREFERENCE LADDER.**

| rung | when | why it is preferred |
| --- | --- | --- |
| **1. width-parametric SYMBOLIC proof** | the fact is true at every width | it **mirrors the spec's own generality** — the standard says "for an N-bit type", and so does the proof |
| **2. kernel `decide`** | small, fixed widths; **the inductive BASE CASE** of a width-parametric argument; any goal genuinely finite and cheap | stays inside the kernel; no extra axiom, no external oracle. Thomas: *decide can be useful for the inductive base case, but width-parametric theorems are usually desired* |
| **3. `bv_decide` / `native_decide`** | cost/benefit favors them — the symbolic proof is out of reach or disproportionate | fastest to obtain; carries the largest trust and information cost |

**Rung 1 is the spec-mirror principle applied to PROOFS**, which is why it
heads the ladder rather than merely being tidy. A tier that mirrors a
clause quantified over widths, and then proves it one width at a time, has
silently narrowed the claim its own §5.5 manifest says it makes. Both rungs
are live on the pinned toolchain and the contrast is one line each: `∀ w,
∀ x : BitVec w, x + 0#w = x` closes symbolically for **every** width, while
`bv_decide` closes the same fact at width 8 **only**.

**PERMITTED USES CARRY THEIR RECEIPT, AT THE USE SITE.** Any rung-3 use
carries (a) its `#print axioms` line and (b) a **one-line justification**
naming why rungs 1 and 2 were not taken. Both live **at the theorem**,
never in a project-wide setting: **the trust boundary is per-theorem and
visible, never ambient.** A reader auditing one theorem must be able to see
its full trust cost without leaving the file — which is principle II's
whole point, applied to the one place the library can widen what the kernel
is asked to believe.

**AND THE RECEIPT ITSELF CAN LIE — measured, with the mode pinned.**
`#print axioms` on a declaration whose **STATEMENT** failed to elaborate
prints

    'foo' does not depend on any axioms

— **the cleanest possible line, meaning the opposite of what it says.**
Reproduced on the pinned toolchain: a theorem whose statement is ill-typed
prints exactly that **even when its proof is literally `sorry`**, because
the declaration was recovered before the proof was ever checked against it.

The mode matters, so it is recorded rather than generalized. Measured, four
failure modes:

| failure | `#print axioms` says |
| --- | --- |
| unsolved goals | `[sorryAx]` — honest |
| body type error | `[sorryAx]` — honest |
| explicit `sorry` | `[sorryAx]` — honest |
| **error in the STATEMENT** | **`does not depend on any axioms`** — lies |

Three of four are honest, and **the one that lies is the most dangerous
case**: a mis-elaborated *statement* means the theorem does not say what
its author thinks, and the axiom line arrives to reassure them. So:

> **An axiom print is meaningful ONLY from a zero-error elaboration.**
> Every quoted axiom line is paired with the file's clean-elaboration
> status, or it is not evidence.

This is the §5.4 instrument contract applied to the receipts themselves —
*every refusal path RUN, not admired* — and it generalizes past this
policy: any triad line, coverage count or `#guard` batch quoted from a file
that did not elaborate cleanly is quoting the error recovery, not the
tree.

**THE HISTORICAL CONTRACT STANDS AS RECORDED FACT.** `AGENTS.md` states
*"Never `sorry`, `admit`, or `native_decide` — anywhere, ever"*, and the
tree honors it: **zero real uses**, verified — all twelve occurrences of
the identifier are prose *recording its absence*. That contract is the
existing estate's and it is not weakened retroactively; **this policy
governs NEW work.** Where the two meet — a new theorem in an existing
file — the file's contract wins, because a file that advertises "no
`native_decide` appears anywhere in this tier" must stay true or stop
saying so. `AGENTS.md`'s line is owned by whoever maintains it, and
reconciling it with this ladder is that owner's edit, flagged here rather
than made silently.

**THE ALIGNMENT WORTH NAMING: SoftFloat's layer 2 IS this preference
embodied.** §3.5.1 specifies it as `round mode (exactRational …)` over a
**width-parametric** `Format` — one statement covering `binary32` and
`binary64` — rather than as per-width bit algorithms. That design was
chosen before this policy was written, which is the useful kind of
corroboration: the ladder is describing what the family already does when
it is thinking clearly.

**The prices are being measured.** The structures-census lane is building
the **width-crossover table** — where rung 1's effort stops beating rung
3's runtime — and this section should cite it when it lands. Until then the
ladder is an ordering, not a threshold, and a lane that needs a threshold
should say so rather than guess one.

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
| SystemVerilog | `Sv` | spec-mirror — IEEE 1800 | `SV2017`, `SV2023` — **PROPOSED** | pyslang frontend; a simulator | **public `sv-tests`** (see below) | **CONSOLIDATION** — 8 166 lines, **98 theorems**, dormant but verified working |
| WebAssembly | `Wasm` | spec-mirror — W3C core **+ official suite** | **PROPOSED** | the reference interpreter **and the `.wast` runner** | the official `.wast` suite | founding |
| ECMAScript | `Es` | spec-mirror — ECMA-262 **+ official suite** | **PROPOSED** | an engine **and test262's harness** | test262 | founding — blocked on SoftFloat (§3.5.3) |
| Ada | `Ada` | spec-mirror — ISO/IEC 8652 **+ official suite** | **`Ada2022`** (spec head) **and `Ada2012`** (suite edition) — RATIFIED | a GNAT toolchain **and the ACATS grader** | **ACATS 4.2**, 4 188 tests | founding — **version pair FORCED** |
| RISC-V | `Rv` | spec-mirror — RISC-V ISA | **PROPOSED** | the ISA oracle | `harness/rv` | consolidation — 2 041 lines |
| Verilog-A | `VerilogA` | extraction — OpenVAF | — | OpenVAF | `Examples/verilog-a` | consolidation — 606 lines |
| SPICE | `Spice`/`Circuit` | extraction — ngspice | — | ngspice | `Examples/spice` | active — 27 675 lines, separate architecture (§6.1) |

The last three carry no edition token today. That is allowed and it is
what §1.4 rules on: **a language earns version directories when its tier
claims an edition, not before.**

**ADA IS THE FIRST TIER TO DECLARE TWO EDITION TOKENS AT FOUNDING, and it
did not choose to.** The ARM is **Ada 2022**; the official suite's baseline
is **ACATS 4.2**, which states in its own modification list that it covers
**Ada 2012**, and no 5.x exists. So the suite is two editions behind the
standard, and **a "conforms to Ada 2022" claim can never be scored against
the official corpus** — any Ada-2022-only feature is outside it by
construction. The version sibling this document asks for is therefore
forced: `Ada2012` is what can be scored, `Ada2022` is the spec-side head.

That is **the exact inverse of the C tier's shape**, where the standard
moved and the suites followed. Here the *suite* is the pinned artifact and
the *spec* is the moving one — and the family's layout convention has to
work in both directions, which §1.1's four laws do without amendment
(`LeanModels/Ada/Ada2012/` says exactly what it is). Ada is also the
validation of §1.4's "pay the directory level early" ruling: a tier that
must carry two editions from its first commit has no cheap moment to add
the level later.

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

*The consolidation order.* The SV lane is §2.4's pattern applied a second
time, and it should run in the pattern's order: **census the IEEE
1800-2017 → 2023 delta FIRST**, then let the numbers place the files. The
expectation, recorded before the measurement so it can be wrong, is a
**thick trunk** with 2023's additions in a thin `SV2023/` that does not
disturb it — the same shape C measured at 933 trunk lines of 934.

*The maturity.* The SV tier is **not greenfield**: `LeanModels/Sv/` is
**8 166 lines** (measured) with a differential harness recorded green
against Icarus, dormant rather than absent. Labelling it "founding" would
have priced a rebuild of work that exists and passes.

**Its theorem count is SETTLED at 98, and adopted because it was
REPRODUCED.** The SV charter states the rule — `theorem`/`lemma`
declarations plus `example`s — and under that rule this document counts
**93 + 5 = 98 exactly**. The earlier disagreement was never about the tree:
93 was the same measurement under a narrower rule that omitted the five
`example`s. A number is adopted here when a second rule reproduces it, not
when a neighbour asserts it, and this one now is.

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

This is the trunk of §2.4's **thin siblings over a thick shared trunk**,
and the placement rule is that section's first clause: **a file moves into
a sibling only when a measurement convicts it.** The default is the trunk,
and the burden of proof is on the sibling.

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

### 2.4 THE RULING: THIN SIBLINGS OVER A THICK SHARED TRUNK

**Mechanism: the measured INTERSECTION lives once, in the version-neutral
layer; everything an edition decides lives WHOLE in that edition's own
directory. Editions are siblings. Neither is the base of the other, and
no definition takes a version parameter.**

**The pattern has a name so that tiers apply it uniformly: THIN SIBLINGS
OVER A THICK SHARED TRUNK.** The trunk is `LeanModels/<Lang>/`; the
siblings are `LeanModels/<Lang>/<Ver>/`, and they should be **small** —
if a sibling is thick, either the editions really do differ that much
(measure and prove it) or the census was not run. Three clauses make it
operational.

**(1) CENSUS-GATED PLACEMENT. A file enters a sibling directory only when a
MEASUREMENT convicts it of edition-sensitivity — never prophylactically.**
The C tier supplies *both* halves of the precedent, and the failed half is
the more instructive one. This document originally convicted `convert` of
being C23-mandated; had that been acted on, a file would have moved into
`C23/` **for nothing**, since §6.3.1.3p3 is word-for-word identical across
the editions (§1.3). The verified conviction — `IntTy.minVal`, on C23
§6.2.6.2p2 — moves **exactly one definition**, and **933 of 934 lines stay
in the trunk**. Prophylactic siblings are how a thick trunk silently
becomes two thin ones.

**(2) THEOREMS PROVE ONCE ON THE TRUNK** and serve every edition that
imports it. A sibling carries a theorem only when the FACT it states is
edition-decided. This is where the pattern pays: the expensive artifact in
this repository is not the definition but the proof estate, and a trunk
theorem is proved once for all editions rather than re-proved per sibling.

**(3) THE ONE HONEST FORK — stated as a boundary so nobody engineers around
it.** When a shared DATATYPE changes SHAPE between editions, the type and
its consumers **must** fork. The measured instance is `PyErr`: 3.9 encodes
zero-division as two nullary constructors, 3.11 splits it three ways, and
that is a change of ARITY, not of a value. No sharing mechanism is sound
there — a delta layer cannot override a constructor list, and a version
parameter would infect every consumer's type. **Duplication is correct
exactly where no sharing mechanism is sound**, and this is that place. A
clever workaround at this boundary is a bug being introduced, not avoided.

**What was refuted stays refuted.** This is not base+delta layering
readmitted under a friendlier name, and it is not version-parameterization.
**The sharing comes from TRUNK PLACEMENT — from where a file lives — not
from a mechanism that relates two files.** Nothing inherits, nothing
overrides, nothing takes an edition argument; a sibling that needs a trunk
definition imports it, and that is the whole of the coupling.

**The SV cleanup is the pattern's second application**, and it should be
run in the pattern's order: **census the IEEE 1800-2017 → 2023 delta
first**, on the model of §2.1's clause instrument, and let the numbers place
the files. The expectation — worth recording *before* the measurement so it
can be wrong — is a **thick trunk**, with 2023's additions living in a thin
`SV2023/` that does not disturb it. If the census says otherwise, the
census wins.

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
* `Run σ α` has **exactly ONE lane consumer: Python** — 15 files under
  `LeanModels/Python/` plus 6 under `Examples/python/`. **SystemVerilog,
  C, RISC-V, Circuit, Spice and Verilog-A are all zero.**

  **CORRECTION, and the error is one this document warns about
  elsewhere.** An earlier revision claimed *"Python (16 files) and
  SystemVerilog (3)"*. The SV three were `grep -rl '\bRun\b'` matching the
  **English word** at the head of a docstring — `/-- Run one comb-phase
  process…` — in files whose actual outcome type is SV's own
  `inductive Res` (`Sv/Semantics.lean:85`). A bare-word grep over a corpus
  that contains prose is not a type census. The C tier's own charter
  records the mirror-image lesson — *grep an operator sort's constructors
  **without** the leading dot* — and this is that trap from the other side.
  Re-derived type-aware (`: Run`, `Run.ok`/`.exn`/`.timeout`/`.unsupported`,
  `Run <Type>`), the SV count is **0** and Python's is **15**.

  **And the right answer was already in this document.** §0.2's inventory
  table records SystemVerilog's outcome type as `Sv.Res α` — correctly —
  three hundred lines above the bullet that called SV a `Run` consumer. The
  failure was not a missing measurement but **two measurements of the same
  fact that were never checked against each other.** That is precisely what
  §5.5's manifest does for clause citations, and it is an argument for
  doing the same to this document's own load-bearing counts.
* Re-derived today, and **grown since §L35 priced the move**: `Run.`
  appears **1282** times (was 1251), `: Run` **160** times (was 143),
  across **31** files (was 24).

**Everything else the C lane "reused" is METHOD, not code** — and the C
charter says so itself. That is not a failure; a method that transfers
entire is the most valuable thing this repository has. But it means the
shared substrate is **one structure — `Span` — with two lane consumers
(Python and C)**, while the outcome type that the whole architecture is
argued around has **one**. A document that spoke of either as an
established platform would be describing something that does not exist.

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

   **READ THE MODE OUT OF THE ARTEFACT, never out of an ambient setting**,
   and the SV lane's §L67 sharpened this to **three edges** worth copying:
   the **schema version**, the **top module**, and the **source-path
   spelling**. All three are properties of the envelope in hand, and each
   is a place a tool can silently assume instead of asking — a
   configured-elsewhere default, an implied entry point, a path normalized
   one way here and another way there. An envelope that cannot answer
   "which mode am I?" from its own bytes is one whose consumers will
   disagree about it, which is the same failure `language_version`
   (§1.5) fixes for editions and `profile_id` fixes for the C ABI.
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
    (§3.4). One `SemM` — `ExceptT ρ (StateT W Halt)`, in that order — one
    `WPMonad` instance, the default `mvcgen`. No language writes a vcgen
    **on the fuel-free fragment**; at the fuel-recursive points each
    language still assembles its own threshold form, which the pilot
    measured and §3.4 states as the bound.
12. **Component #2 — SoftFloat** (§3.5). Layer 1 (executable bit-level
    IEEE 754) is supplied by core Lean on the pinned toolchain; layer 2
    (the round-of-exact spec algebra) is the family's build. Consumed by
    C, Wasm, SV, Python, Go — and **blocking** for ECMAScript.
13. **Component #3 — the concurrency pattern** (§3.6). Schedule as an
    explicit parameter, executable counterexample schedules, the DRF-SC
    fence, three proof-burden tiers. One pattern, one citation per
    language. **The monad carries one process's step; `W` carries the
    concurrency** — a language whose processes suspend defunctionalizes the
    continuation into `W` (§3.6 (1a)), because the stack has no suspension
    case and cannot be given one.

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

**The question: does every language need its own `mvcgen`?** The answer is
a SPLIT, measured by the pilot (`docs/mvcgen-pilot.md`, §L61): **no on the
fuel-free fragment, yes at the fuel-recursive points.** This section states
the design; every number in it is the pilot's, and where the pilot refuted
this document it says so.

**Layer 1 — one monad family, and the layer ORDER is load-bearing.**

```lean
-- (illustrative — the substrate shape, not yet in the tree)
abbrev SemM (W : Type) (ρ : Type) := ExceptT ρ (StateT W Halt)
```

**This document first wrote `StateT W (ExceptT ρ Halt)`, and that is
REFUTED BY `rfl`.** `StateT` outside `ExceptT` **discards the state on a
raise** — the shapes are `W → Except ρ (α × W)` versus
`W → (Except ρ α × W)`, and only the second keeps `W` on the error branch.
`Run`'s `.exn` RETAINS state, and `PyPost.err` is state-aware for exactly
that reason. The difference is visible in the `PostShape` barrel:
`ρ → ULift Prop` in the wrong order, **`ρ → W → ULift Prop`** in the right
one. **The wrong order cannot state the tier's own error postcondition.**
One line, load-bearing for every tier written against the sketch, and
verified here independently before propagating.

**`Run σ α` IS that stack — proved, not asserted.** The pilot's
`ofRun`/`toRun` are mutually inverse in 22 lines, and both stacks `#synth`
a `WPMonad` with **zero instances written**. That **retires the 2026-08-13
spike's obstacle 1** — *"`Run` is not a monad"* — as a permanent obstacle:
it was a fact about the tree, not about the type. The instance was never
unavailable; it was never asked for.

**What this stack CANNOT do, stated here because it is a property of the
substrate and not of any tier: it cannot SUSPEND.** `ExceptT ρ (StateT W
Halt) α` unfolds to `W → (Except ρ α × W)` — an `α`, or a `ρ`, plus a `W`,
and no third case. `StateT` is run-to-completion. A language whose
processes pause mid-body must defunctionalize, putting the continuation in
`W` and making suspension a return value; **§3.6 (1a) is the pattern and
SystemVerilog is the worked example.** A tier that plans a suspension
*effect* is planning something the types do not admit.

Two design constraints make this work and both are load-bearing:

* **Fuel stays OUT of the monad — and the reason is stronger than this
  document originally gave.** It is an index on the step function
  (`step : Nat → Stmt → SemM W ρ Unit`), not a reader layer. The original
  argument was that `fuelMono` and the ∃-threshold form are theorems about
  a *family* of programs. The pilot's is harder: **fuel as a monad layer
  does not typecheck.** Fuel's job is to BE the recursion argument, so
  hidden in state it is not an argument and the interpreter fails to show
  termination — *"`loopF` does not take any (non-fixed) arguments"*. The
  alternative does not merely cost something; it does not exist.
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
`⦃P⦄ … ⦃Q⦄` notation. **No toolchain bump is required.** The pilot
independently confirmed this and sharpened the import boundary: `@[spec]`
is a BUILTIN attribute needing no import — which is why `Logic.lean`
already uses it — while the tactic needs `import Std.Do` and
`import Std.Tactic.Do`, both CORE modules, so `lakefile.toml` and
`lake-manifest.json` are untouched. **The expensive experiment this
document anticipated does not exist.**

Per-language work under this scheme is then: **the World type, the error
type, the primitive step functions, and `@[spec]` lemmas for the
primitives.** Priced by the pilot against C's six design pieces: **≈2 type
declarations + 2 `abbrev`s + ~14 `@[spec]` lemmas ≈ 120 lines**, against
the **5 343 lines** of Python-specific walker (`VC` 546 + `VC2` 939 +
`VCTactic` 3 371 + `LoopTactic` 487) that the shared substrate replaces.
The three never-pooled refusal causes (§5.2) cost nothing — one `.except`
layer each, free by composition — and **C's drain amendment at its 181
short-circuit sites IS the altitude law, at 3 `@[spec]` lemmas.**

**THE ASTERISK ON THAT PRICE, measured by the rebuild lane, and it is the
difference between a demo and an estimate.** The pilot's headline
elaboration economics — a `mvcgen` step in **568 ms** against a gate whose
real-interpreter counterpart takes 24 s — were measured against the
**SHALLOW TWIN**. Run the *identical statement* against the **FAITHFUL
interpreter** and it **does not close at 8 M heartbeats (~14 minutes)**.
The gap is not overhead; it is **exactly the fidelity the twin dropped** —
the nine-step name-resolution chain and the five-way assign fork. Two
smaller faithful gates do close, at **~10–11 s**.

So the economics are real but their granularity is different:
**mvcgen's advantage holds at ARM-LEVEL granularity, given sufficient
`@[spec]` coverage.** The per-language estimate above should therefore be
read as a floor that **grows toward per-arm lemma sets** — ~14 lemmas is
what the *shape* costs, not what a faithful interpreter's every arm costs.
A founding lane should price its `@[spec]` set per interpreter arm and
treat 120 lines as the entry fee.

> **A PERFORMANCE NUMBER MEASURED ON A TWIN IS A CLAIM ABOUT THE TWIN.**

That is the exact twin of §3.4 clause (b)'s adequacy warning, and the two
should be read together: a second semantics owes an **adequacy** theorem
before its *correctness* transfers, and owes a **re-measurement** before
its *performance* transfers. The twin was built to be fast in precisely the
places the real interpreter is slow, so its timings describe the
simplification, not the tier.

**THE BOUND, and it corrects this document.** §3.2 item 11 said *"no
language writes a vcgen."* That is **true on the fuel-free fragment and
false at the fuel-recursive points.** At a symbolic fuel `F`, `mvcgen`
returns the goal **unchanged after 1 m 31 s**: nothing in `Std.Do` relates
two runs at DIFFERENT fuels, because `Triple` is unary on one program while
`fuelMono` and the threshold form are about a family. So
`∃ t, ∀ F ≥ t, run F = .ok w v` is **neither produced nor consumed by
mvcgen; it is assembled around it**, and each language still writes its own
threshold assembly at `call`, loop, and generator points. The saving is
real, it is large, and it is **bounded** — and a tier choosing the
∃-fuel route is choosing the route mvcgen cannot walk, which is a decision
to take consciously and with these numbers.

**The fuel-free fragment is nonetheless large**, which is why the saving
survives the bound: the pilot's `evalM` is structural on `Expr`, and a
whole real gate's slice carries no fuel numeral anywhere. Fuel is owed only
at `callIn` / `execWhile` / `execFor` / `heapEq` / generators.

**Four laws to adopt now, at zero cost**, all measured rather than
proposed:

* **Altitude lemmas persist, and `@[spec]` is their registry.** With the
  primitives UNFOLDED, `mvcgen` leaves **259+ VCs** and `mvcgen_trivial`
  fails outright; the same goal with four `@[spec]` triples leaves **12**,
  all pure, and closes. The family's existing altitude lemmas do not merely
  resemble `Spec` lemmas — they transliterate.
* **Specs must be OUTPUT-DETERMINED.** A spec taking the answer as an INPUT
  made mvcgen unify the result metavariable with a loop ACCUMULATOR — a
  wrong-but-typechecking instantiation — leaving 23 VCs with dependent
  metavariables. Restated so the value is determined by the postcondition:
  3 and 12 VCs, none.
* **`Triple` does not frame the state.** A read-only primitive must SAY it
  leaves the state unchanged; Std ships `Triple.observe` for it.
* **Never a bare polymorphic `throw`** — route every refusal through a
  NAMED primitive with its own `@[spec]` lemma. This is forced by a real
  Std bug the pilot found in twenty lines (`Spec.throw_Except` carries
  binders its conclusion does not determine, yielding universe-level
  metavariables), and **it is what this family wants anyway**: a refusal is
  a first-class notion here, and mvcgen rewards making it one.

**Risk, recorded straight:** `mvcgen` warns on every invocation that it is
experimental and should be avoided in production, and one Std bug surfaced
in twenty lines of probing.

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

**Three caveats. Two are retired by measurement; the third is now a
standing rule with a named blocker.**

1. **Deep embedding — RETIRED.** `mvcgen` reasons about Lean programs in a
   monad, and the interpreter's SUBJECT is an AST value, so the vcgen must
   unfold the interpreter's `match` on a **pinned** program literal. The
   pilot did exactly this on a real gate and it worked, closing the same
   fact with the gate's own fourteen premises.
2. **Toolchain — RETIRED**, twice independently (this document's probes and
   the pilot's census). `Std.Do` is already at the pin.
3. **Python is MID-CAMPAIGN. The policy is MIGRATION BY EROSION** — not a
   permanent exemption. An earlier draft of this section said Python
   *"bridges, does not migrate"*, which reads as a standing no and is not
   defensible: the right question is not *whether* but *in what order and
   against what evidence.* Three clauses.

   **(a) NOT DURING THE SUNFISH CAMPAIGN — because an interpreter rewrite
   RE-FOUNDS every landed theorem.** The precedent is measured and it is
   sobering in the direction that matters. §L15's re-pin changed only the
   OBJECT PROGRAM — not the interpreter — and its blast radius still came
   in **four files wider than priced**; what moved was **78 pinned spans,
   61 synthesized `<genexpr@n>` names, three censuses and 15 battery
   pairs**, and the law it produced is *"price a re-pin by its `#guard`s,
   not by its `theorem`s."* The reassuring half is that **every theorem
   re-elaborated green with no edit** — because the interpreter did not
   move. **A monadic migration moves exactly the thing the re-pin held
   fixed**, so the half that saved §L15 is the half that would not apply,
   across every file carrying proof edits. That is the cost of doing it
   *now*; it is not an argument that it is wrong.

   **(b) THE BRIDGE IS THE FIRST HALF OF ANY SOUND MIGRATION, not an
   alternative to one.** The monadic form is a **second semantics**, so
   replacing the tier's definition — validated by **1 394 differential
   cases** — without `twinAgrees` would be an **untrusted definition
   change**, and §0.1's first principle makes that the one move the
   architecture forbids: the definition is the trusted artifact, and
   swapping it on the strength of a convenience layer inverts the trust
   boundary. So adequacy is not a toll gate peculiar to Python; it is the
   required artifact on **every** route:

   > **Any route that introduces a second semantics owes an adequacy
   > theorem, and the differential corpus does not discharge it.**

   Whether the monadic form ends up the bridge's far side or the tier's
   new definition, `twinAgrees` is on the critical path either way — which
   is precisely why building the bridge is progress toward migration
   rather than a detour around it. The pilot's twin is already executable
   and `#guard`ed on a fixture, and its fidelity gap to the real
   interpreter is exact and stated (name resolution consults the static
   globals fold first; the twin's does not).

   **(c) AFTER ADEQUACY, THE QUESTION DISSOLVES.** With `twinAgrees`
   proved, the two forms are **interchangeable by theorem**, and the
   migration needs no flag day: new Python work is written monadic, old
   theorems transport across the bridge **on demand** — paid per theorem
   that is touched anyway, never as a campaign — and the deep interpreter
   retires **gradually, or never**. "Never" then costs nothing, because a
   proved interchangeability makes the surviving form an implementation
   detail rather than a commitment. Erosion, not migration.

   **The SEQUENCING rationale, which is about risk and not about Python.**
   `mvcgen` warns on every invocation that it is experimental, and one Std
   bug surfaced in twenty lines of probing (§3.4). **New tiers should
   absorb that tactic churn; the flagship estate should not.** A tier with
   no landed theorems pays nothing when a tactic's behavior shifts under
   it; a tier with a campaign's worth pays in re-proofs. So the order is
   the risk-weighted one, and it happens to also be the cheap one.

   §3.8 applies the same trigger discipline to `Run`.

**The pilot is landed** (`docs/mvcgen-pilot.md`, §L61) and its numbers
replace this section's earlier estimates throughout. Its recommendation:
new tiers adopt the substrate and use mvcgen on the fuel-free fragment,
**deciding fuel's fate BEFORE writing the interpreter** — which is a
founding-checklist item, not an afterthought.

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
else — **rung 1 and rung 2 of §0.1 II(a), with no `native_decide` needed
and none used.** Core ships **1856 lines**
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
Kernel-reducible and **width-parametric down to the packed boundary**
(`binary32` and `binary64` are instances, not definitions — see the
requirement below). **Supplied by core Lean on the pinned toolchain**; the family's work here is to
*depend on it deliberately* — pin the interface, gate the reduction
behaviour with `#guard`s the way every other tier gates its primitives, and
own the residue core does not cover.

**Layer 2 — the SPEC ALGEBRA, and this is what the family builds.**
Per-operation correctness, proved once, in IEEE form:

```
-- (illustrative — the obligation shape, not a tree file)
op_correct (fmt : Format) :
    bitOp fmt x y  =  round fmt mode (exactRational (val x ∘ val y))
```

##### WIDTH-PARAMETRICITY IS A REQUIREMENT, not a description

Thomas's directive, and it is binding on this component: **the Float spec
must be width-parametric — no hard-coded mantissa or exponent widths.**
Three clauses.

**(1) THE SPEC ALGEBRA IS DEFINED OVER A GENERAL `Format`** — exponent
width and significand width as **parameters**, mirroring IEEE 754-2019's
own §3.3 parameterization of formats. **`binary16`, `binary32`, `binary64`
and `binary128` are INSTANCES, never separate definitions.** A component
that defines "the binary64 algebra" and later "the binary32 algebra" has
already lost: it will carry two of every lemma, and the second copy is
where the divergence lives.

**(2) EVERY LAYER-2 THEOREM IS STATED OVER THE GENERAL `Format`.** The
`op_correct` family above quantifies over `fmt`. Width-specific theorems
are admissible **only** as (a) instance corollaries — `op_correct
binary64` — or (b) `decide`-closed **base cases** of an induction, per the
§0.1 II(a) ladder. Thomas, precisely: *decide can be useful for the
inductive base case, but width-parametric theorems are usually desired.*
This is the ladder's rung 1 with a component-specific edge: here, rung 1 is
not merely preferred, it is the deliverable.

**(3) THE ALIGNMENT CHECK ON CORE, verified at the pin — and it has a
boundary that must be FLAGGED, not absorbed.** Measured:

| core declaration | width-parametric? |
| --- | --- |
| `Float.Model.Format` (`mantissaBitsWithoutImplicit`, `exponentBits`, `numBits`) | **yes** — the parameter record itself |
| `Float.Model.Format.Valid : (spec : Format) → BitVec spec.numBits → Prop` | **yes** — indexed by the format |
| `Float.Model.UnpackedFloat` | **yes** — width-agnostic; the format is not baked into the type |
| `UnpackedFloat.add : Format → UnpackedFloat → UnpackedFloat → UnpackedFloat` | **yes** — takes the format as an ARGUMENT |
| `Float.Model` | **NO** — zero parameters; hard-codes `Format.binary64` and `UInt64` |
| `Float32.Model` | **NO** — zero parameters; hard-codes `Format.binary32` and `UInt32` |

**Core's parametricity stops at the PACKED boundary.** Everything beneath
it — the format record, validity, the unpacked representation, the
rounding layer and the operations — is parametric; the two packed wrapper
types are per-width duplicates. So the requirement has a concrete
consequence: **build layer 2 over `Format` + `UnpackedFloat`, never over
`Float`/`Float32`.** The moment a theorem mentions `Float`, it has
hard-coded binary64 and clause (2) is violated silently, because nothing
about the statement looks width-specific.

Where core's API forces a fixed width, the tier **flags it** — records the
declaration, states which widths it therefore cannot serve, and either
wraps it parametrically or reports the gap. It does **not** absorb the
fixed width into our layer and call the result general.

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
   predicates, and the exact-rational bridge they all share, **all stated
   over a general `Format`**. This is the component; everything below is a
   widening.
2. **Conversions** — integer↔float both directions, and format-to-format
   conversion **stated between two general `Format`s**, of which
   `binary32 ↔ binary64` (what Wasm needs) is an instance.
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

#### (1a) `SemM` CANNOT SUSPEND — and the pattern survives only because the
process table lives in W

**The claim above is true and its stated reason was wrong**, which the SV
lane's scheduler-first assessment found by trying to build on it. The
sentence *"nothing about the monad changes"* invites the reading that **the
monad carries the concurrency. It does not. `W` does.**

**The structural fact, verified by `rfl` on this substrate:**
`ExceptT ρ (StateT W Halt) α` unfolds to `W → (Except ρ α × W)`. A
computation therefore returns **an `α`, or a `ρ`, plus a `W` — and there is
no third case.** `StateT` is **run-to-completion**: there is nowhere in the
monad to put *"paused here, resume at this point."* No arrangement of these
transformers gains a suspension case, because none of them has one.

So any language whose processes **pause mid-body** — SystemVerilog's
`@`/`#`/`wait`, and eventually goroutines blocked on a channel — cannot
express suspension as an *effect*. It must **DEFUNCTIONALIZE**:

* **the continuation becomes DATA in `W`.** SV's form is
  `ProcState.residual`: the remaining statement list. This is **sound
  because suspension points are SYNTACTIC** — a process can only pause at a
  construct the grammar names, so "where it paused" is a position in the
  program text and not an arbitrary closure. A language that could suspend
  at an arbitrary point would need a real continuation and this trick would
  not be available.
* **the interpreter becomes a SCHEDULER LOOP** over the process table,
  rather than a walk down one process's body.
* **suspension is a RETURN VALUE, not an effect** — the step function
  answers *"finished"* or *"suspended, with this residual"*, and the
  scheduler decides who runs next.

**The worked example, and its shape is the reusable part.** SV's
`stepProcess` **subsumes `execStmts` by one field** plus an
adequacy-shaped lemma: the ordinary statement walker is the special case
where nothing suspends, and the lemma says so. That is the migration path
for any tier that starts sequential and later grows concurrency — you do
not rewrite the walker, you generalize its return type and prove the old
one is the non-suspending case.

**What this costs the pattern: nothing — and that is the test it passed.**
Schedule-as-parameter survives, `fuelMono` survives, the ∃-fuel form
survives, `mvcgen` survives. But they survive **because the process table
is World data**, so the scheduler loop is an ordinary state-threading
program over it. Stated precisely: **the monad carries one process's step;
`W` carries the concurrency.** A tier that reads §3.6 as "the monad handles
threads" will design a suspension effect, discover it cannot exist, and pay
for the discovery.

**For the Go tier specifically: goroutine parking takes this exact shape**
— a blocked goroutine's continuation becomes data in `W`, the runtime
becomes a scheduler loop, and parking is a return value. Go's charter
should **cite this section rather than re-derive it**; the only thing that
differs is which syntactic constructs are the suspension points.

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

**But they differ sharply on what a RACY program means, and the scoreboard
must not pool them.** C says a data race is **undefined behavior** — no
bound at all — so a racy C program is REFUSE(`undefined`), as above. Go
does **not**: it bounds what a racy program may observe, describing the
permitted outcomes rather than surrendering. **A racy Go program is
therefore not a refusal — it is a MEMBERSHIP site**, scored by §5.1's rule:
the model is right when its outcome is *one of* the permitted ones. Mapping
Go's bounded races onto C's `undefined` would refuse programs Go fully
describes, which is the same false-statement-about-the-language error §4.3
catches at Ada's bounded errors. Same shape, three languages.

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

**Trigger — RE-DERIVED, because its old premise was false.** This section
previously leaned on `Run` already having two lane consumers. It does not:
type-aware, it has **one, Python** (§3.1). So the trigger cannot be "when
the second consumer appears" as an observation about the present; it is a
statement about which lane arrives first, and there are now **three
candidates**:

| candidate | status | would it trigger? |
| --- | --- | --- |
| **C's M2 inch 4** — statements + `CWorld` | planned; C is at inch 1 and uses its own `CRes` at the value layer | yes — the first C code that needs a world |
| **the rebuild lane's `SemM`** | in flight; **`SemM` is not in the tree** (checked) | yes — and it arrives as the stack, not as bare `Run` |
| a third tier adopting the outcome type | none proposed | yes |

**Whichever lands first is the trigger**, and the rule is unchanged in
substance: the move happens when a second consumer exists, not before
(the ingester tier does not mention `Run`) and not after (a second
interpreter landing with its own copy of `Run` is a defect, not a design).

**And §3.4 collapses this question into one.** Since `Run σ α` is
*proved* to be `ExceptT ρ (StateT W Halt)` — `ofRun`/`toRun` mutually
inverse — "move `Run` to `Core`" and "land the `SemM` substrate" are **the
same landing**, not two. The destination should therefore be the stack,
with `Run` as its established view, so that a lane arriving via either
route finds one artifact.

**And the price is drifting.** §L35 measured 1251 `Run.` sites in 24
files; today it is **1282 in 31**. The deferral is correct and it is not
free, which is precisely why the trigger is a named landing rather than a
judgement call.

The `Run.exn` payload decision (`Run σ ε α`, or C's terminal riding in α)
belongs to the same inch. It is the one place the outcome type is not yet
neutral, and naming it here is cheaper than discovering it there.

---

## 4 THE AUTHORITY TAXONOMY

### 4.1 THREE authorities, and a tier declares which it is

**SPEC-MIRROR.** A published normative document defines the language. The
model's obligation is **clause coverage**: every clause the tier claims is
realized by a declaration, and the manifest says which. C, SystemVerilog,
WebAssembly, ECMAScript, Ada, RISC-V.

**INTERPRETER-EXTRACTION.** No normative document is the authority in
practice. The model's obligation is **differential agreement**, and the
differential harness IS the extraction instrument. Python, SPICE,
Verilog-A.

**OFFICIAL-SUITE — the third, added by the Ada charter.** A conformance
suite exists that is owned by **neither the standards body nor an
implementer**, and ships **its own published grading rules and its own
grading tool**. Then the model's obligation on a suite test is neither
"match the document" nor "match an implementation" but **"earn the verdict
the suite's grader assigns"**, and the suite owner is the authority for
what that verdict is.

This is a genuinely distinct third thing and the family already contained
both poles without naming the axis. **C has no official suite at all** —
`docs/c23-goal.md` opens by saying so, which is precisely why its goal had
to be *restated* as agreement with three compiler projects' regression
histories, and why its §4.3 has to warn that a high score means "agrees
with what these projects test", not "conforms to ISO 9899". **Ada has the
opposite**: ACATS 4.2, 4 188 tests, six named classes, and an
implementation-neutral event-trace format that makes the grade
machine-readable rather than a convention. ECMAScript's test262 is the same
shape. The axis is worth naming because it changes what a tier can honestly
claim: only an official-suite tier can say "conformant" and mean the word
the way the language's own community uses it.

The distinction is about where a rule comes from, not about rigor. The
Python lane's `docs/completeness.md` §5 records five grammar verdicts read
off the source and MEASURED otherwise — four of them became the cheapest
rung on its ladder. Under extraction, `print(5 ^ 3)` outranks any reading.

### 4.2 The precedence rule where BOTH exist

Most spec languages also have a dominant implementation, and every tier in
this family that mirrors a spec also runs one: C targets ISO 9899 and runs
clang; SystemVerilog targets IEEE 1800 and runs pyslang plus a simulator;
Wasm, ECMAScript and Ada all have reference implementations.

> **The SPEC is the target. The IMPLEMENTATION is the oracle for
> behavior. The SUITE OWNER is the authority for the expected VERDICT. A
> divergence between any two is a FINDING — recorded with both citations,
> and it blocks none of them.**

The third clause is the Ada charter's amendment, and it is not a
restatement of the second. An implementation tells you *what happened*; a
suite's grader tells you *whether that counts as passing*, and those are
different questions the moment a test is graded on anything but byte
equality — which ACATS's six classes routinely are (a class-C test passes
on `PASSED` **or** `NOT-APPLICABLE`; a class-D test passes on the exact
answer **or** a capacity error). Reading a grader's rule off an
implementation's behavior would silently substitute one authority for
another.

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
| **Ada** | errors detected before run time; errors detected at run time; **bounded error**; erroneous execution; unspecified; implementation-defined | **FILLED** (`docs/ada-charter.md` §1.5). Run-time errors are an ORDINARY OUTCOME — `Run.exn` already has the shape. **Erroneous execution is cause 2, `undefined`, exactly.** Unspecified is cause 4 plus the ∀-parameter shape. Implementation-defined is the PROFILE, verbatim. **Bounded error fits none of the four**, and pre-run-time errors are not a refusal at all but a VERDICT the family lacked — both below. |

**THE PREDICTION IN THIS ROW WAS ANSWERED, AND IT WAS WRONG.** This
document predicted that if a fifth REFUSE cause were needed, Ada is where
it would show. **It does not show. The gap is one level up, in the
scoreboard** — §5.2's four causes are complete, and §5.1's verdicts were
not.

Walk a bounded-error site against the four causes and each fails for its
own reason. The construct is in the vocabulary (not cause 1). The standard
**describes the behavior fully** — the possible effects of a bounded error
are enumerated for each such error — so calling it `undefined` would be a
**false statement about the language**, and false in the expensive
direction: it refuses a program the standard fully describes, and that
refusal is then indistinguishable on the scoreboard from a tier gap, which
is the exact conflation §5.2 exists to prevent. Nothing is missing from the
slice (not cause 3). And it is **not cause 4**, because the quantifier is
the other way round: cause 4 is about ORDERS and its obligation is that
*every* admissible order gives the same observable — a **∀**; a bounded
error admits several OUTCOMES and its obligation is that the model's
outcome is *some* permitted one — an **∃**.

That ∀/∃ flip is the whole finding, and it lands in §5.1.

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
| **MATCH** | the model ran to completion and its observable **satisfies the site's expectation** — see the membership rule below |
| **REFUSE** | the model declined, loudly and fuel-independently. FOUR disjoint causes (§5.2), reported separately |
| **DIVERGE** | the model produced an observable and it does NOT satisfy the expectation. The invariant violation. Zero, always |
| **TIMEOUT** | fuel exhausted. The only exhaustion outcome; never conflated with REFUSE |

**THE DIVERGE TEST IS NOT EQUALITY AT EVERY SITE**, and this document said
it was. The Ada charter's bounded-error analysis (§4.3) forces the
correction:

> **At a site where the language enumerates several permitted outcomes,
> MATCH is MEMBERSHIP in that set, not equality with one oracle's
> observable. Two conforming implementations may disagree there and both
> be right.**

Scoring byte equality at such a site **manufactures DIVERGEs** — and
DIVERGE is the family's zero-tolerance invariant, so a manufactured one is
not a cosmetic error: it either halts a lane chasing a non-bug or, worse,
trains the lane to tolerate DIVERGE rows. Refusing instead is no better; it
is a coverage loss the language does not require, at a site the standard
describes completely.

**Three consequences, and the first two are what make it cheap.** The
permitted set is a **per-site datum** the tier carries, not a new verdict
name — the vocabulary above is unchanged. Equality is the **degenerate
case**, a singleton set, so every existing site is already correct under
the membership rule and nothing needs revisiting. And MATCH stops meaning
"agrees with the oracle" and starts meaning "is permitted", which is the
honest reading and the one an official-suite tier (§4.1) needs anyway,
since ACATS class C passes on `PASSED` *or* `NOT-APPLICABLE` and class D on
the exact answer *or* a capacity error.

**This class is not Ada-specific, which is why it belongs here.** It is
exactly what **Go's racy programs** need (§3.6): Go bounds what a racy
program may observe instead of surrendering to UB the way C does, so a racy
Go program is a membership site and not a refusal. C's
`unspecified`-but-enumerated sites are the same shape again. Ada found it
because Ada's standard *enumerates* the permitted effects per error where
other languages leave the enumeration implicit — the finding was always
there, and Ada's rigor apparatus made it visible.

**Two ways to carry the per-site datum, and neither is chosen here** —
it is Thomas's, and the Ada charter lists it as an open decision: the site
carries its permitted set explicitly, or the scoreboard consults a
predicate supplied by the tier. The architecture only fixes that the test
IS membership.

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
* **every quoted number is paired with the elaboration status of the file
  it came from** (§0.1 II(a)): a triad line, coverage count, `#guard` batch
  or axiom print taken from a file that did not elaborate cleanly is
  quoting the error recovery, not the tree — and at least one such line
  reads *cleaner* than the truth rather than dirtier;
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

### 5.6 SUITES drive SCOPE; ONE EXEMPLAR drives the PROOF LIBRARY

A tier needs corpora for two different jobs, and conflating them is how a
repository acquires pet programs. The split below is **measured, not
sentimental**, and it is §0.1's principle II — the library grows by demand
— given an actual selection rule.

**SUITES DRIVE SCOPE, because they walk the spec systematically and a
single program cannot.** The evidence is the C tier's own numbers, and they
cut against the program: `ctwin/sunfish.c`'s **accidental** 45-kind
vocabulary already clears **357 of 431 freestanding suite tests — 83%**
before a single construct is added. Read carefully, that is an argument for
the suite, not for the program: the suite finds *the same vocabulary* the
flagship happened to use **plus the remainder**, and it finds the remainder
in the standard's own order rather than in one author's. A driver program
can only ever discover its own vocabulary.

**The counter-evidence is in the tree too, and it is the Python tier.** Its
coverage grew **sunfish-shaped**: `>>`, `^`, unary `+` and `~` were absent
not because they were hard — they landed in the session that censused them
— but because nothing the flagship needed had asked for them, and three of
the four were *recorded as deferred in three different places*, none of
which was where a person looks to ask "which operators run?". It took
`print(5 ^ 3)` — a census, not a program — to find them. That is the cost
the completeness workstream exists to correct, and it is what scope-by-
driver-program buys you.

**THE CARVE-OUT, and it is why one exemplar is still required.** Suite
scoring exercises the **DEFINITION**: a verdict runs the interpreter and
compares an observable, and **no theorem is involved**. It therefore cannot
find a gap in the proof **LIBRARY**, because it never asks the library for
anything. Library gaps surface only under **deep end-to-end theorems about
one real program**, and every law this repository has minted traces to
exactly that:

* the **altitude lemmas** — prove it once at the chain with every operand
  symbolic — and their price tag, 259+ VCs unfolded against 12;
* **computed-shape / residue-spelling**: index premises must be spelled in
  the interpreter's own residue, not in the reader's preferred normal form;
* the **vacuity catches** — a carried-over receiver shape makes every
  statement about it vacuous and cannot break a build;
* `Bracket.SubtreeWrites`, whose docstring records an arm **"UNINHABITABLE
  at the shipped code"** — a distinction only a real program's heap can
  draw;
* `settle_needs_futility`, a **countermodel** exhibiting the schedule that
  refutes the theorem-without-its-premise.

Not one of those could have come from a single-construct witness, and that
is not an accident of history: **single-construct witnesses are shallow by
design.** A witness that exercises one production establishes that the
production is reachable; it cannot produce a law about *composing twenty of
them under a heap*, because it never composes anything.

**THE POLICY.**

> **Suites drive scope. ONE theorem-worthy EXEMPLAR per tier drives the
> proof library. The exemplar is chosen for its THEOREM — never for its
> authorship — and no program is commissioned as a driver for its own
> sake.**

Applied: **SystemVerilog's exemplar is the floating-point divider** (§3.5.2
states its theorem, and it factors through the shared vertex rather than
comparing two models). **C's is `ctwin/sunfish.c`, which already served**
and is not re-commissioned — its job was the construct census and the
ingestion milestone, both done. A founding lane names its exemplar by
stating the theorem it intends to prove; if it cannot state one, it does
not need an exemplar yet, and its suite is enough.

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
   trap 'rm -rf /tmp/ls-build.lock || echo "LOCK RELEASE FAILED" >&2' EXIT
   ```

   Release promptly. **Never hold it while thinking or editing.**

   **AMENDMENT 2 — the release must be `rm -rf` and its status must be
   checked.** A `rmdir` release composed with an owner-stamp file inside
   the lock directory **fails silently**: `rmdir` refuses a non-empty
   directory, the `trap` swallows the status, and the lock leaks — after
   which every other lane blocks forever on a lock nobody holds. This
   happened. `rm -rf` removes the directory whatever it contains, and the
   `|| echo` makes a failed release loud instead of invisible.
2. **Cap parallelism under the lock — but NOT with `-j4` on this lake**,
   where it is an argument error rather than a flag. Use the environment
   or the toolchain's accepted spelling, and verify the command runs
   before relying on it; a build that dies on its own flags is a build
   that did not happen.

   **Exit status 143 is a RESOURCE KILL**, not a build failure — the OS
   terminated the job. Re-read it as "the machine was oversubscribed",
   check the lock discipline, and never record it as a red build.
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
   §5.4 contract. **The scope corpus is a SUITE** (§5.6) — a driver program
   discovers only its own vocabulary. A tier may also name **one exemplar**
   for its proof library, and names it **by stating the theorem**; if it
   cannot state one, it does not need an exemplar yet.
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
7. **DECIDE FUEL'S FATE — before writing the interpreter, not after.**
   The fuel-free fragment gets the shared `mvcgen` for ~120 lines of
   `@[spec]`; the fuel-recursive points get the tier's own threshold
   assembly and mvcgen makes no progress there (§3.4). The two routes
   differ in the interpreter's TYPE, so this is not a proof-layer choice
   that can be deferred — and a tier that also wants kernel-reducible runs
   (`#guard` at a fixed fuel) has already chosen fuel.
8. **`LeanModels/<Lang>/<Ver>/`** — the semantics, and the manifest
   (§5.5) starting the same day.

---

## 8.5 REGISTERED CAMPAIGN ITEM — THE ADEQUACY MILESTONE

Named here so it is a scheduled artifact rather than a standing caveat.

> **`twinAgrees` — an adequacy theorem relating the deep interpreter to its
> monadic twin over the same AST.**

* **Why it is a milestone and not a caveat.** It is the required artifact
  on **every** route (§3.4 clause b): the bridge's far side and any future
  definition swap both go through it, so it is on the critical path whether
  or not Python ever migrates. Until it exists, the monadic form is a
  second semantics with no theorem tying it to the trusted one, and §0.1
  principle I forbids treating it as the definition.
* **What does NOT discharge it.** The differential corpus. **1 394 cases**
  validate the *deep* interpreter against CPython; they say nothing about
  the twin, and the twin's fidelity gap is already known and stated (name
  resolution consults the static globals fold first; the twin's does not).
  An executable twin joining `diff_test` would buy evidence, not a theorem
  — and would cost a second maintained interpreter under the
  model-matches-code law.
* **GATED ON `bound_refines_fuelModel` closing.** That is the campaign's
  own assembly point — `RecursionStep` first, then
  `bound_refines_fuelModel` — and it is the moment the flagship estate
  stops absorbing re-proof cost from an interpreter change. Starting
  adequacy earlier competes with the campaign for the same files.
* **What it unlocks, priced.** The **5 343-line** substrate saving (§3.4)
  becomes collectable, and §3.4 clause (c)'s erosion begins: new work
  monadic, old theorems transported on demand, the deep interpreter
  retiring gradually or never.

---

## 9 WHAT THIS DOCUMENT DOES NOT DECIDE

* **Whether any of the three new spec tiers is founded, or in what
  order.** The registry rows are PROPOSED and §4.3's observation that
  WebAssembly is the family's best calibration case is an argument, not a
  schedule.
* **WHEN the adequacy milestone starts, and how fast erosion runs.** §3.4
  clause (c) and §8.5 fix the policy — migration by erosion, gated on
  `bound_refines_fuelModel` — but the schedule, and how much old work ever
  transports across the bridge, are the Python lane's on that day's
  numbers.
* **Whether `Run` moves at C's M2 inch 4 or the inch slips.** The trigger
  is fixed (§3.8); the inch is the C lane's.
* **The C lane's three stale citations** (§2.5). Found here, fixed there.
* **`VerilogA.Span`'s rename** (§3.7) — when that lane is next open.
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
